"""開賣提醒小工具

- 可設定多個場次（名稱、購票網址、開賣時間）
- 開賣前 N 分鐘跳出 Windows 通知＋提示音（預設 10 分鐘、1 分鐘）
- 開賣時間一到，通知＋提示音（可勾選是否自動打開購票頁面，預設不開）
- 倒數計時對齊「購票網站伺服器的時間」（失敗時改用 NTP 標準時間）
- 等待期間防止電腦進入睡眠

只負責提醒與開網頁，登入、選位、付款請自行操作。
"""

import ctypes
import email.utils
import http.client
import json
import urllib.parse
import socket
import struct
import subprocess
import sys
import threading
import time
import tkinter as tk
import traceback
import webbrowser
import winsound
from datetime import datetime, timedelta, timezone

TW_TZ = timezone(timedelta(hours=8), "台灣標準時間")  # 固定 UTC+8，不受電腦時區設定影響
from pathlib import Path
from tkinter import messagebox, ttk

# 打包成 exe 後，設定檔放在 exe 旁邊（而不是解壓縮的暫存資料夾）
APP_DIR = Path(sys.executable if getattr(sys, "frozen", False) else __file__).resolve().parent
CONFIG_FILE = APP_DIR / "reminder_config.json"

NTP_SERVERS = ["time.stdtime.gov.tw", "tock.stdtime.gov.tw", "time.google.com", "pool.ntp.org"]
NTP_RESYNC_SEC = 600
DEFAULT_REMIND_MINUTES = [10, 1]
OVERLAY_SECONDS = 30  # 開賣前幾秒在螢幕右上角顯示倒數
TIME_FORMAT = "%Y-%m-%d %H:%M:%S"


# ---------------------------------------------------------------- 時間校正
def query_ntp(server: str, timeout: float = 2.0) -> float:
    """回傳 (NTP 時間 - 本機時間) 的秒數差。"""
    packet = b"\x1b" + 47 * b"\0"
    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
        s.settimeout(timeout)
        t0 = time.time()
        s.sendto(packet, (server, 123))
        data, _ = s.recvfrom(48)
        t3 = time.time()
    secs, frac = struct.unpack("!II", data[40:48])  # transmit timestamp
    server_time = secs - 2208988800 + frac / 2**32
    return server_time - (t0 + t3) / 2


def query_http_date(url: str, samples: int = 8) -> tuple:
    """用網站回應的 Date 標頭估算 (網站時間 - 本機時間)。

    Date 標頭只精確到秒，所以連發幾次請求、錯開送出的小數秒位置，
    每次都能得到時間差的上下限，取交集後可縮到約 0.1 秒內。
    回傳 (時間差, 精確度)。
    """
    parts = urllib.parse.urlsplit(url)
    conn_cls = http.client.HTTPSConnection if parts.scheme == "https" else http.client.HTTPConnection
    conn = conn_cls(parts.hostname, parts.port, timeout=5)
    path = parts.path or "/"
    lo, hi = -float("inf"), float("inf")
    try:
        conn.request("HEAD", path)  # 第一次先建立連線（TLS 握手慢，不列入計算）
        conn.getresponse().read()
        for i in range(samples):
            t0 = time.time()
            conn.request("HEAD", path)
            resp = conn.getresponse()
            t1 = time.time()
            resp.read()
            date = resp.getheader("Date")
            if not date:
                raise OSError("網站沒有回傳 Date 標頭")
            server_sec = email.utils.parsedate_to_datetime(date).timestamp()
            # CDN（如 CloudFront）快取命中時 Date 是存入快取的舊時間，要加上 Age 秒數
            age = resp.getheader("Age")
            if age and age.strip().isdigit():
                server_sec += int(age)
            # 網站時間落在 [server_sec, server_sec+1)，且發生在本機 t0~t1 之間
            lo = max(lo, server_sec - t1)
            hi = min(hi, server_sec + 1 - t0)
            time.sleep(0.15 + ((i * 0.37) % 1) * 0.3)  # 錯開小數秒，讓上下限收斂
    finally:
        conn.close()
    if lo > hi:  # 網路延遲忽快忽慢造成矛盾，取中間值即可
        lo, hi = hi, lo
    return (lo + hi) / 2, (hi - lo) / 2


class Clock:
    def __init__(self):
        """初始化時間校正資料與校正來源。"""
        self.offset = 0.0
        self.source = "尚未校正（使用電腦時間）"
        self.last_sync = 0.0
        self.url = None  # 要對齊時間的網站（下一個場次的網址）

    def now(self) -> float:
        """回傳套用校正差值後的目前時間。"""
        return time.time() + self.offset

    def sync(self) -> None:
        """優先透過購票網站校正時間，失敗時改用 NTP 伺服器。"""
        url = self.url
        if url:
            host = urllib.parse.urlsplit(url).hostname
            try:
                offset, err = query_http_date(url)
                self.offset = offset
                self.source = f"網站 {host}（與電腦時間差 {offset:+.2f} 秒，精確度 ±{err:.2f} 秒）"
                self.last_sync = time.time()
                return
            except (OSError, http.client.HTTPException, ValueError, TypeError):
                pass  # 網站校時失敗就改用 NTP
        for server in NTP_SERVERS:
            try:
                self.offset = query_ntp(server)
                note = "網站校時失敗，改用 " if url else "尚未輸入購票網址，暫用 "
                self.source = f"{note}NTP {server}（與電腦時間差 {self.offset:+.2f} 秒）"
                self.last_sync = time.time()
                return
            except OSError:
                continue
        self.source = "校正失敗，暫用電腦時間"
        self.last_sync = time.time()


# ---------------------------------------------------------------- 通知
def keep_awake(on: bool) -> None:
    """控制 Windows 是否允許系統進入睡眠或關閉螢幕。"""
    ES_CONTINUOUS, ES_SYSTEM_REQUIRED = 0x80000000, 0x00000001
    flags = ES_CONTINUOUS | (ES_SYSTEM_REQUIRED if on else 0)
    try:
        ctypes.windll.kernel32.SetThreadExecutionState(flags)
    except Exception:
        pass


def _xml_escape(s: str) -> str:
    """將文字中的 XML 特殊字元轉成對應的實體字元。"""
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
             .replace('"', "&quot;").replace("'", "&apos;"))


def toast_command(title: str, body: str) -> list:
    """建立 Windows 系統通知所需的 PowerShell 命令。

    Args:
        title: 通知標題。
        body: 通知內容。

    Returns:
        可直接傳給 subprocess.Popen 的 PowerShell 命令參數清單。
    """
    xml =(f'<toast><visual><binding template="ToastGeneric">'
           f"<text>{_xml_escape(title)}</text><text>{_xml_escape(body)}</text>"
           f"</binding></visual></toast>")
    xml = xml.replace("'", "''")  # 放進 PowerShell 單引號字串，避免 $ 等符號被解讀
    ps = (
        "[Windows.UI.Notifications.ToastNotificationManager, Windows.UI.Notifications, ContentType=WindowsRuntime] | Out-Null;"
        "[Windows.Data.Xml.Dom.XmlDocument, Windows.Data.Xml.Dom.XmlDocument, ContentType=WindowsRuntime] | Out-Null;"
        "$x = New-Object Windows.Data.Xml.Dom.XmlDocument;"
        f"$x.LoadXml('{xml}');"
        "$app = '{1AC14E77-02E7-4E5D-B744-2EB1AE5198B7}\\WindowsPowerShell\\v1.0\\powershell.exe';"
        "[Windows.UI.Notifications.ToastNotificationManager]::CreateToastNotifier($app).Show("
        "[Windows.UI.Notifications.ToastNotification]::new($x))"
    )
    return ["powershell.exe", "-NoProfile", "-WindowStyle", "Hidden", "-Command", ps]


def windows_toast(title: str, body: str) -> None:
    """透過 Windows PowerShell 送出系統通知（不需額外安裝套件）。"""
    try:
        subprocess.Popen(toast_command(title, body),
                         creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
    except OSError:
        pass


def play_sound(times: int = 3) -> None:
    """在背景執行緒中播放指定次數的系統提醒音。"""
    def run():
        """重複播放提示音並保留播放間隔。"""
        for _ in range(times):
            winsound.MessageBeep(winsound.MB_ICONEXCLAMATION)
            time.sleep(0.6)
    threading.Thread(target=run, daemon=True).start()


# ---------------------------------------------------------------- 設定檔
def load_config() -> dict:
    """讀取設定檔；若檔案不存在或格式錯誤則回傳預設設定。"""
    try:
        return json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {"remind_minutes": DEFAULT_REMIND_MINUTES, "events": []}


def save_config(cfg: dict) -> None:
    """將設定資料以 UTF-8 格式寫入設定檔。"""
    CONFIG_FILE.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")


# ---------------------------------------------------------------- 介面
class App:
    def __init__(self, root: tk.Tk):
        """初始化主視窗、設定、場次清單與即時提醒排程。"""
        self.root = root
        self.clock = Clock()
        self.cfg = load_config()
        self.cfg.setdefault("remind_minutes", DEFAULT_REMIND_MINUTES)
        self.cfg.setdefault("events", [])
        for ev in self.cfg["events"]:
            ev.setdefault("fired", [])

        root.title("開賣提醒")
        # 依螢幕縮放比例（例如 150%）放大視窗，避免下方清單與按鈕被切掉
        scale = max(1.0, root.winfo_fpixels("1i") / 96)
        root.geometry(f"{int(760 * scale)}x{int(600 * scale)}")
        root.minsize(int(620 * scale), int(520 * scale))

        style = ttk.Style()
        style.configure("Treeview", rowheight=int(22 * scale))
        style.configure("Big.TLabel", font=("Microsoft JhengHei UI", 30, "bold"))
        style.configure("Mid.TLabel", font=("Microsoft JhengHei UI", 12))

        top = ttk.Frame(root, padding=12)
        top.pack(fill="x")
        self.next_name = ttk.Label(top, text="沒有即將開賣的場次", style="Mid.TLabel")
        self.next_name.pack(anchor="w")
        self.countdown = ttk.Label(top, text="--:--:--", style="Big.TLabel")
        self.countdown.pack(anchor="w")
        self.now_label = ttk.Label(top, text="")
        self.now_label.pack(anchor="w")
        self.sync_label = ttk.Label(top, text="")
        self.sync_label.pack(anchor="w")

        form = ttk.LabelFrame(root, text="新增場次", padding=10)
        form.pack(fill="x", padx=12)
        ttk.Label(form, text="名稱").grid(row=0, column=0, sticky="w")
        self.e_name = ttk.Entry(form)
        self.e_name.grid(row=0, column=1, sticky="ew", padx=6, pady=2)
        ttk.Label(form, text="購票網址").grid(row=1, column=0, sticky="w")
        self.e_url = ttk.Entry(form)
        self.e_url.grid(row=1, column=1, sticky="ew", padx=6, pady=2)
        self.syncing = False
        self.sync_finished = False
        self.resync_pending = False
        self._url_job = None
        self.e_url.bind("<KeyRelease>", self.on_url_changed)
        self.e_url.bind("<<Paste>>", lambda e: self.root.after(10, self.on_url_changed))
        self.e_url.bind("<FocusOut>", self.on_url_changed)
        ttk.Label(form, text="開賣時間（台灣時間）").grid(row=2, column=0, sticky="w")
        self.e_time = ttk.Entry(form)
        self.e_time.insert(0, datetime.now(TW_TZ).strftime("%Y-%m-%d 12:00:00"))
        self.e_time.grid(row=2, column=1, sticky="ew", padx=6, pady=2)
        ttk.Label(form, text="提前提醒（分鐘，逗號分隔）").grid(row=3, column=0, sticky="w")
        self.e_remind = ttk.Entry(form)
        self.e_remind.insert(0, ",".join(str(m) for m in self.cfg["remind_minutes"]))
        self.e_remind.grid(row=3, column=1, sticky="ew", padx=6, pady=2)
        form.columnconfigure(1, weight=1)
        self.auto_open = tk.BooleanVar(value=bool(self.cfg.get("auto_open", False)))

        def toggle_auto_open():
            """儲存使用者是否要在開賣時自動開啟購票網頁。"""
            self.cfg["auto_open"] = self.auto_open.get()
            self.save()
        ttk.Checkbutton(form, text="時間到自動開啟購票網頁", variable=self.auto_open,
                        command=toggle_auto_open).grid(row=4, column=0, columnspan=2, sticky="w", pady=(6, 0))
        btns = ttk.Frame(form)
        btns.grid(row=4, column=1, sticky="e", pady=(6, 0))
        ttk.Button(btns, text="測試通知", command=self.test_notify).pack(side="left", padx=4)
        ttk.Button(btns, text="新增", command=self.add_event).pack(side="left")

        lst = ttk.LabelFrame(root, text="已新增的場次（選取後可刪除，按 Delete 鍵或右鍵也可以）", padding=10)
        lst.pack(fill="both", expand=True, padx=12, pady=12)
        # 按鈕列先放在底部，視窗再小也不會被清單擠掉
        row = ttk.Frame(lst)
        row.pack(side="bottom", fill="x", pady=(6, 0))
        ttk.Button(row, text="刪除選取的場次", command=self.delete_selected).pack(side="right")
        ttk.Button(row, text="立即開啟網頁", command=self.open_selected).pack(side="right", padx=4)
        ttk.Button(row, text="重新校時", command=self.start_sync).pack(side="left")
        self.tree = ttk.Treeview(lst, columns=("name", "time", "url"), show="headings", height=5)
        for col, text, w in (("name", "名稱", 160), ("time", "開賣時間", 170), ("url", "網址", 360)):
            self.tree.heading(col, text=text)
            self.tree.column(col, width=w, anchor="w")
        self.tree.pack(fill="both", expand=True)
        self.tree.bind("<Delete>", lambda e: self.delete_selected())
        menu = tk.Menu(root, tearoff=0)
        menu.add_command(label="立即開啟網頁", command=self.open_selected)
        menu.add_command(label="刪除這個場次", command=self.delete_selected)

        def popup(e):
            """在滑鼠右鍵位置顯示場次操作選單。"""
            iid = self.tree.identify_row(e.y)
            if iid:
                self.tree.selection_set(iid)
                menu.tk_popup(e.x_root, e.y_root)
        self.tree.bind("<Button-3>", popup)

        self.refresh_tree()
        self.start_sync()
        keep_awake(True)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.build_overlay()
        self.tick()
        self.overlay_loop()

    # ---- 校時
    def sync_target(self):
        """要對齊的網站：下一個尚未開賣的場次；沒有場次時用輸入框裡的網址。"""
        upcoming = [ev for ev in self.sorted_events() if ev["ts"] > self.clock.now()]
        if upcoming:
            return upcoming[0]["url"]
        typed = self.e_url.get().strip()
        return typed if typed.startswith(("http://", "https://")) else None

    def start_sync(self):
        """啟動時間校正執行緒，並避免重複同時校正。"""
        if self.syncing:
            self.resync_pending = True
            return
        self.syncing = True
        self.clock.url = self.sync_target()
        host = urllib.parse.urlsplit(self.clock.url).hostname if self.clock.url else None
        self.sync_label.config(text=f"正在對齊 {host} 的伺服器時間…" if host else "校時中…")

        def run():
            """在背景執行時間校正並通知主執行緒完成。"""
            try:
                self.clock.sync()
            finally:
                self.sync_finished = True  # 由主執行緒的 tick() 接手（Tk 不能跨執行緒呼叫）
        threading.Thread(target=run, daemon=True).start()

    def _sync_done(self):
        """處理時間校正完成後的介面與待重試狀態。"""
        self.sync_finished = False
        self.syncing = False
        if self.resync_pending:
            self.resync_pending = False
            self.start_sync()

    def on_url_changed(self, _event=None):
        """在網址停止輸入一段時間後，於必要時重新校正時間。"""
        # 輸入網址後（停止輸入 0.8 秒）若要對齊的網站變了，就重新校時
        if self._url_job:
            self.root.after_cancel(self._url_job)

        def check():
            """確認校時目標是否變更並觸發重新校正。"""
            self._url_job = None
            if self.sync_target() != self.clock.url:
                self.start_sync()
        self._url_job = self.root.after(800, check)

    # ---- 場次管理
    def add_event(self):
        """驗證並新增一個開賣場次到設定與畫面清單。"""
        name = self.e_name.get().strip() or "未命名場次"
        url = self.e_url.get().strip()
        if not url.startswith(("http://", "https://")):
            messagebox.showerror("網址錯誤", "請輸入以 http:// 或 https:// 開頭的網址")
            return
        try:
            ts = (datetime.strptime(self.e_time.get().strip(), TIME_FORMAT)
                  .replace(tzinfo=TW_TZ).timestamp())  # 輸入的開賣時間視為台灣時間
        except ValueError:
            messagebox.showerror("時間格式錯誤", "請用 YYYY-MM-DD HH:MM:SS 格式，例如 2026-12-01 12:00:00")
            return
        try:
            mins = sorted({int(x) for x in self.e_remind.get().replace("，", ",").split(",") if x.strip()},
                          reverse=True)
        except ValueError:
            messagebox.showerror("提醒時間錯誤", "請輸入整數分鐘，用逗號分隔，例如 10,1")
            return
        if ts <= self.clock.now():
            if not messagebox.askyesno("時間已過", "這個開賣時間已經過了，還是要加入嗎？"):
                return
        self.cfg["remind_minutes"] = mins
        self.cfg["events"].append({"name": name, "url": url, "ts": ts, "remind": mins, "fired": []})
        self.save()
        self.refresh_tree()
        self.start_sync()  # 下一場可能換了網站，重新對時
        self.e_name.delete(0, "end")
        self.e_url.delete(0, "end")

    def delete_selected(self):
        """刪除清單中目前選取的場次。"""
        ids = {int(i) for i in self.tree.selection()}
        if not ids:
            messagebox.showinfo("刪除場次", "請先在清單中點選要刪除的場次")
            return
        names = "\n".join("・" + ev["name"] for i, ev in enumerate(self.sorted_events()) if i in ids)
        if not messagebox.askyesno("確定刪除？", f"要刪除以下場次嗎？刪除後就不會再提醒。\n\n{names}"):
            return
        self.cfg["events"] = [ev for i, ev in enumerate(self.sorted_events()) if i not in ids]
        self.save()
        self.refresh_tree()
        self.start_sync()

    def open_selected(self):
        """開啟目前選取場次的購票網址。"""
        events = self.sorted_events()
        for i in self.tree.selection():
            webbrowser.open(events[int(i)]["url"])

    def sorted_events(self):
        """依開賣時間排序場次並回傳排序後的清單。"""
        self.cfg["events"].sort(key=lambda e: e["ts"])
        return self.cfg["events"]

    def refresh_tree(self):
        """重新整理場次清單的表格內容。"""
        self.tree.delete(*self.tree.get_children())
        for i, ev in enumerate(self.sorted_events()):
            self.tree.insert("", "end", iid=str(i), values=(
                ev["name"], datetime.fromtimestamp(ev["ts"], TW_TZ).strftime(TIME_FORMAT), ev["url"]))

    def save(self):
        """將目前設定寫入檔案，失敗時顯示錯誤訊息。"""
        try:
            save_config(self.cfg)
        except OSError as e:
            messagebox.showerror("儲存失敗", str(e))

    # ---- 提醒
    def notify(self, title: str, body: str, popup: bool = False):
        """送出系統通知、播放提示音，並依需求置頂主視窗。"""
        windows_toast(title, body)
        play_sound()
        if popup:
            self.root.deiconify()
            self.root.attributes("-topmost", True)
            self.root.lift()
            self.root.after(3000, lambda: self.root.attributes("-topmost", False))

    def test_notify(self):
        """送出測試通知，以確認通知與提示音功能正常。"""
        self.notify("開賣提醒（測試）", "如果你看到這則通知並聽到提示音，提醒功能正常。", popup=True)

    def check_events(self, now: float):
        """檢查各場次是否到達提前提醒或開賣時間並觸發提醒。"""
        changed = False
        for ev in self.cfg["events"]:
            remaining = ev["ts"] - now
            for m in ev.get("remind", DEFAULT_REMIND_MINUTES):
                key = f"m{m}"
                # 只在提醒時間點附近 60 秒內觸發，避免重開程式時補發過期提醒
                if key not in ev["fired"] and 0 < remaining <= m * 60 and remaining > m * 60 - 60:
                    ev["fired"].append(key)
                    changed = True
                    self.notify(f"{ev['name']}：{m} 分鐘後開賣",
                                "請先登入帳號、準備好付款方式。", popup=(m <= 1))
            if "open" not in ev["fired"] and -60 < remaining <= 0:
                ev["fired"].append("open")
                changed = True
                if self.auto_open.get():
                    webbrowser.open(ev["url"])
                    self.notify(f"{ev['name']}：開賣了！", "已為你打開購票頁面。", popup=True)
                else:
                    self.notify(f"{ev['name']}：開賣了！", "請到購票頁面購票。", popup=True)
        if changed:
            self.save()

    # ---- 右上角倒數小視窗（開賣前 OVERLAY_SECONDS 秒出現）
    def build_overlay(self):
        """建立開賣前顯示於螢幕右上角的倒數視窗。"""
        ov = tk.Toplevel(self.root)
        ov.withdraw()
        ov.overrideredirect(True)          # 無邊框
        ov.attributes("-topmost", True)    # 永遠在最上層
        ov.attributes("-alpha", 0.92)
        ov.configure(bg="#B00020")
        self.ov_title = tk.Label(ov, text="", fg="white", bg="#B00020",
                                 font=("Microsoft JhengHei UI", 11, "bold"))
        self.ov_title.pack(padx=16, pady=(8, 0))
        self.ov_time = tk.Label(ov, text="", fg="white", bg="#B00020",
                                font=("Consolas", 40, "bold"))
        self.ov_time.pack(padx=16, pady=(0, 2))
        hint = tk.Label(ov, text="點一下關閉", fg="#FFD6DC", bg="#B00020",
                        font=("Microsoft JhengHei UI", 8))
        hint.pack(pady=(0, 6))
        for w in (ov, self.ov_title, self.ov_time, hint):
            w.bind("<Button-1>", self.dismiss_overlay)
        self.overlay = ov
        self.overlay_ev = None
        self.overlay_dismissed = set()
        self.overlay_visible = False

    def dismiss_overlay(self, _event=None):
        """關閉目前倒數視窗，並記錄該場次不再重複顯示。"""
        if self.overlay_ev is not None:
            self.overlay_dismissed.add(self.overlay_ev)
        self.overlay.withdraw()
        self.overlay_visible = False

    def overlay_loop(self):
        """週期性更新倒數視窗，並攔截例外以避免排程中斷。"""
        try:
            self._update_overlay()
        except Exception:
            traceback.print_exc()
        finally:
            self.root.after(100, self.overlay_loop)  # 每 0.1 秒更新；出錯也不中斷

    def _update_overlay(self):
        """依目前時間更新倒數視窗的內容與顯示狀態。"""
        now = self.clock.now()
        target = None
        for ev in self.sorted_events():
            remaining = ev["ts"] - now
            if -5 < remaining <= OVERLAY_SECONDS and ev["ts"] not in self.overlay_dismissed:
                target = (ev, remaining)
                break
        if target:
            ev, remaining = target
            self.overlay_ev = ev["ts"]
            self.ov_title.config(text=ev["name"])
            self.ov_time.config(text=f"{remaining:.1f}" if remaining > 0 else "開賣！")
            if not self.overlay_visible:
                self.overlay.update_idletasks()
                w = max(self.overlay.winfo_reqwidth(), 220)
                x = self.overlay.winfo_screenwidth() - w - 24
                self.overlay.geometry(f"{w}x{self.overlay.winfo_reqheight()}+{x}+24")
                self.overlay.deiconify()
                self.overlay.lift()
                self.overlay_visible = True
        elif self.overlay_visible:
            self.overlay.withdraw()
            self.overlay_visible = False

    def tick(self):
        """執行一輪提醒檢查並安排下一個整秒的排程。"""
        try:
            self._tick()
        except Exception:
            traceback.print_exc()
        # 對齊到下一個整秒，讓倒數跳動準確；出錯也一定排下一次，避免提醒停擺
        delay = int((1 - (self.clock.now() % 1)) * 1000) + 5
        self.root.after(delay, self.tick)

    def _tick(self):
        """更新校時狀態、檢查提醒，並刷新倒數與時間顯示。"""
        if self.sync_finished:
            self._sync_done()
        now = self.clock.now()
        if time.time() - self.clock.last_sync > NTP_RESYNC_SEC and self.clock.last_sync:
            self.clock.last_sync = time.time()  # 避免校時期間重複觸發
            self.start_sync()
        self.check_events(now)

        label = "購票網站時間（台灣 UTC+8）：" if "網站 " in self.clock.source else "標準時間（台灣 UTC+8）："
        self.now_label.config(text=label + datetime.fromtimestamp(now, TW_TZ).strftime(TIME_FORMAT))
        if self.clock.last_sync and not self.syncing:
            self.sync_label.config(text="時間來源：" + self.clock.source)

        upcoming = [ev for ev in self.sorted_events() if ev["ts"] > now]
        if upcoming:
            ev = upcoming[0]
            left = int(ev["ts"] - now + 0.999)
            d, rem = divmod(left, 86400)
            h, rem = divmod(rem, 3600)
            m, s = divmod(rem, 60)
            text = (f"{d} 天 " if d else "") + f"{h:02d}:{m:02d}:{s:02d}"
            self.next_name.config(text=f"下一場：{ev['name']}")
            self.countdown.config(text=text)
        else:
            self.next_name.config(text="沒有即將開賣的場次")
            self.countdown.config(text="--:--:--")

    def on_close(self):
        """確認是否關閉視窗；關閉前停止防止睡眠並釋放主視窗。"""
        if any(ev["ts"] > self.clock.now() for ev in self.cfg["events"]):
            if not messagebox.askyesno("確定關閉？", "還有場次尚未開賣，關閉後就不會提醒了。確定要關閉嗎？"):
                return
        keep_awake(False)
        self.root.destroy()


def main():
    """檢查執行環境、初始化主視窗並啟動 Tkinter 事件迴圈。"""
    if sys.platform != "win32":
        print("此工具僅支援 Windows")
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
