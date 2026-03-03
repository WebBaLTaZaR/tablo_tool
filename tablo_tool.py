import configparser
import os
import sys
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox
import ctypes
from ctypes import wintypes

import serial
import serial.tools.list_ports

try:
    import pymysql
except Exception:
    pymysql = None

try:
    import pystray
    from PIL import Image, ImageDraw
except Exception:
    pystray = None
    Image = None
    ImageDraw = None


DELIMITER = 0xF0
DEFAULT_BAUD = 9600
REPEAT_COUNT = 7
REK_COM_BAUD = 1200
REK_COM_REPEAT = 3
REK_COM_MODE = 2
PROTOCOL_RS485 = "rs485"
PROTOCOL_REK_COM = "rek_com"
PROTOCOL_LABELS = {
    "RS-485 (gekata)": PROTOCOL_RS485,
    "COM табло (rek)": PROTOCOL_REK_COM,
}
PROTOCOL_LABEL_BY_ID = {value: key for key, value in PROTOCOL_LABELS.items()}


def build_rs485_frame(addr: int, text: str, blink: bool) -> bytes:
    if len(text) != 4:
        raise ValueError("Для RS-485 текст должен быть ровно из 4 символов")
    blink_byte = 10 if blink else 0
    payload = [DELIMITER, 0, addr, blink_byte] + [ord(c) for c in text]
    return bytes(payload)


def build_rs485_blank(addr: int) -> bytes:
    return bytes([DELIMITER, 0, addr, 15, 32, 32, 32, 32])


def build_rs485_change_addr(old_addr: int, new_addr: int) -> bytes:
    return bytes([DELIMITER, 255, old_addr, old_addr, old_addr, new_addr, new_addr, new_addr])


def rs485_send(port: str, data: bytes, baud: int = DEFAULT_BAUD):
    ser = None
    try:
        ser = serial.Serial(port, baud)
        ser.write(data * REPEAT_COUNT)
        ser.flush()
        time.sleep(1.0)
    finally:
        if ser:
            ser.close()


def _rek_bcd(value: int) -> int:
    if not (0 <= value <= 99):
        raise ValueError("Для COM табло (rek) номер окна должен быть в диапазоне 0..99")
    return ((value // 10) << 4) | (value % 10)


def _rek_bits(value: int, width: int) -> bytes:
    return bytes(0x7F if (value >> bit) & 1 else 0x00 for bit in range(width))


def build_rek_com_frame(window_no: int, number: int, mode: int = REK_COM_MODE) -> bytes:
    if not (0 <= window_no <= 99):
        raise ValueError("Для COM табло (rek) номер окна должен быть в диапазоне 0..99")
    if not (0 <= number <= 999):
        raise ValueError("Для COM табло (rek) номер должен быть в диапазоне 0..999")
    if not (0 <= mode <= 15):
        raise ValueError("Режим COM табло (rek) должен быть в диапазоне 0..15")
    ones = number % 10
    tens = (number // 10) % 10
    hundreds = (number // 100) % 10
    op_bcd = _rek_bcd(window_no)
    chk = ((ones << 4) + mode + tens + (hundreds << 4) + op_bcd + 1) & 0xFF
    payload = bytearray([0x55])
    payload.extend(_rek_bits(mode, 4))
    payload.extend(_rek_bits(ones, 4))
    payload.extend(_rek_bits(tens, 4))
    payload.extend(_rek_bits(hundreds, 4))
    payload.extend(_rek_bits(op_bcd, 8))
    payload.extend(_rek_bits(chk, 8))
    return bytes(payload)


def build_rek_com_clear(window_no: int, mode: int = REK_COM_MODE) -> bytes:
    if not (0 <= window_no <= 99):
        raise ValueError("Для COM табло (rek) номер окна должен быть в диапазоне 0..99")
    op_bcd = _rek_bcd(window_no)
    chk = (((0x0F) << 4) + mode + 0x0F + ((0x0F) << 4) + op_bcd + 1) & 0xFF
    payload = bytearray([0x55])
    payload.extend(_rek_bits(mode, 4))
    payload.extend(_rek_bits(0x0F, 4))
    payload.extend(_rek_bits(0x0F, 4))
    payload.extend(_rek_bits(0x0F, 4))
    payload.extend(_rek_bits(op_bcd, 8))
    payload.extend(_rek_bits(chk, 8))
    return bytes(payload)


def rek_com_send(port: str, data: bytes, repeat: int = REK_COM_REPEAT):
    ser = None
    try:
        ser = serial.Serial(
            port=port,
            baudrate=REK_COM_BAUD,
            bytesize=serial.EIGHTBITS,
            parity=serial.PARITY_NONE,
            stopbits=serial.STOPBITS_ONE,
            timeout=1,
        )
        for _ in range(max(1, repeat)):
            ser.write(data)
            ser.flush()
            time.sleep(0.05)
    finally:
        if ser:
            ser.close()
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Табло — управление")
        self.resizable(False, False)
        self.configure(bg="#F4F1EC")
        self._scan_thread = None
        self._scan_stop = threading.Event()
        self._db_thread = None
        self._db_stop = threading.Event()
        self._db_active = {}
        self._last_orders_id = 0
        self.addr_by_var = tk.StringVar(value="cabinet_id")
        self.text_mode_var = tk.StringVar(value="queue_num_4")
        self.addr_map = {}
        self.map_path = self._get_map_path()
        self.settings_path = self._get_settings_path()
        self._tray = None
        self._tray_thread = None
        self._cred_target = "tablo_tool:db_password"

        self._apply_theme()
        self._build_ui()
        self._refresh_ports()
        self._load_map()
        self._load_settings()
        self._update_protocol_ui()
        self.protocol("WM_DELETE_WINDOW", self.on_exit)
        self.after(300, self._auto_start)

    def _apply_theme(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass

        style.configure(
            "TFrame",
            background="#F4F1EC",
        )
        style.configure(
            "TLabel",
            background="#F4F1EC",
            foreground="#1E1E1E",
            font=("Segoe UI", 10),
        )
        style.configure(
            "Header.TLabel",
            background="#F4F1EC",
            foreground="#2E2A25",
            font=("Segoe UI Semibold", 12),
        )
        style.configure(
            "TButton",
            font=("Segoe UI Semibold", 10),
            padding=6,
        )
        style.map(
            "TButton",
            background=[("active", "#E6D9C8")],
        )
        style.configure(
            "Primary.TButton",
            background="#E3B973",
            foreground="#1E1E1E",
            font=("Segoe UI Semibold", 10),
            padding=7,
        )
        style.map(
            "Primary.TButton",
            background=[("active", "#D7AA5C")],
        )
        style.configure(
            "TEntry",
            padding=4,
        )
        style.configure(
            "TCheckbutton",
            background="#F4F1EC",
            font=("Segoe UI", 10),
        )
        style.configure(
            "TCombobox",
            padding=4,
        )

    def _auto_start(self):
        # Auto-start DB monitoring on launch
        try:
            self.on_db_start()
        except Exception:
            pass
        # Minimize to tray after start
        self.after(300, self._hide_to_tray)

    def _build_ui(self):
        pad = {"padx": 10, "pady": 6}

        frm = ttk.Frame(self, padding=10)
        frm.grid(row=0, column=0, sticky="nsew")

        notebook = ttk.Notebook(frm)
        notebook.grid(row=0, column=0, sticky="nsew")

        db_frame = ttk.Frame(notebook, padding=12)
        test_frame = ttk.Frame(notebook, padding=12)
        notebook.add(db_frame, text="Связь с БД")
        notebook.add(test_frame, text="Тест Табло")

        ttk.Label(db_frame, text="Подключение", style="Header.TLabel").grid(
            row=0, column=0, columnspan=3, sticky="w", padx=8, pady=(0, 6)
        )

        ttk.Label(db_frame, text="Режим табло:").grid(row=1, column=0, sticky="e", **pad)
        self.protocol_label_var = tk.StringVar(value=PROTOCOL_LABEL_BY_ID[PROTOCOL_RS485])
        self.protocol_combo = ttk.Combobox(db_frame, textvariable=self.protocol_label_var, width=20, state="readonly", values=list(PROTOCOL_LABELS.keys()))
        self.protocol_combo.grid(row=1, column=1, sticky="w", **pad)
        self.protocol_combo.bind("<<ComboboxSelected>>", lambda _e: self._update_protocol_ui())

        ttk.Label(db_frame, text="COM-порт:").grid(row=2, column=0, sticky="e", **pad)
        self.port_var = tk.StringVar(value="COM3")
        self.port_combo = ttk.Combobox(db_frame, textvariable=self.port_var, width=12)
        self.port_combo.grid(row=2, column=1, sticky="w", **pad)
        ttk.Button(db_frame, text="Обновить", command=self._refresh_ports).grid(row=2, column=2, **pad)

        sep1 = ttk.Separator(db_frame, orient="horizontal")
        sep1.grid(row=3, column=0, columnspan=3, sticky="ew", padx=8, pady=6)

        ttk.Label(db_frame, text="База данных", style="Header.TLabel").grid(
            row=4, column=0, columnspan=3, sticky="w", padx=8, pady=(2, 6)
        )

        ttk.Label(db_frame, text="Хост:").grid(row=5, column=0, sticky="e", **pad)
        self.db_host_var = tk.StringVar(value="localhost")
        ttk.Entry(db_frame, textvariable=self.db_host_var, width=14).grid(row=5, column=1, sticky="w", **pad)

        ttk.Label(db_frame, text="Порт:").grid(row=6, column=0, sticky="e", **pad)
        self.db_port_var = tk.StringVar(value="3306")
        ttk.Entry(db_frame, textvariable=self.db_port_var, width=14).grid(row=6, column=1, sticky="w", **pad)

        ttk.Label(db_frame, text="Пользователь:").grid(row=7, column=0, sticky="e", **pad)
        self.db_user_var = tk.StringVar(value="")
        ttk.Entry(db_frame, textvariable=self.db_user_var, width=14).grid(row=7, column=1, sticky="w", **pad)

        ttk.Label(db_frame, text="Пароль:").grid(row=8, column=0, sticky="e", **pad)
        self.db_pass_var = tk.StringVar(value="")
        ttk.Entry(db_frame, textvariable=self.db_pass_var, width=14, show="*").grid(row=8, column=1, sticky="w", **pad)

        ttk.Label(db_frame, text="База:").grid(row=9, column=0, sticky="e", **pad)
        self.db_name_var = tk.StringVar(value="")
        ttk.Entry(db_frame, textvariable=self.db_name_var, width=14).grid(row=9, column=1, sticky="w", **pad)

        self.process_existing_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(db_frame, text="Обработать уже существующие", variable=self.process_existing_var).grid(
            row=10, column=1, sticky="w", **pad
        )

        ttk.Label(db_frame, text="Интервал (с):").grid(row=11, column=0, sticky="e", **pad)
        self.db_poll_var = tk.StringVar(value="0.5")
        ttk.Entry(db_frame, textvariable=self.db_poll_var, width=14).grid(row=11, column=1, sticky="w", **pad)

        ttk.Button(db_frame, text="Старт", style="Primary.TButton", command=self.on_db_start).grid(
            row=12, column=0, **pad
        )
        ttk.Button(db_frame, text="Стоп", command=self.on_db_stop).grid(row=12, column=1, **pad)

        ttk.Label(test_frame, text="Инструменты", style="Header.TLabel").grid(
            row=0, column=0, columnspan=3, sticky="w", padx=8, pady=(2, 6)
        )

        ttk.Label(test_frame, text="Адрес:").grid(row=1, column=0, sticky="e", **pad)
        self.test_addr_var = tk.StringVar(value="1")
        ttk.Entry(test_frame, textvariable=self.test_addr_var, width=14).grid(row=1, column=1, sticky="w", **pad)

        self.test_value_label = ttk.Label(test_frame, text="Текст (4 симв.):")
        self.test_value_label.grid(row=2, column=0, sticky="e", **pad)
        self.test_text_var = tk.StringVar(value="0001")
        ttk.Entry(test_frame, textvariable=self.test_text_var, width=14).grid(row=2, column=1, sticky="w", **pad)

        self.test_blink_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(test_frame, text="Мигание", variable=self.test_blink_var).grid(row=3, column=1, sticky="w", **pad)

        ttk.Button(test_frame, text="Отправить", command=self.on_test_send).grid(row=4, column=0, **pad)
        ttk.Button(test_frame, text="Очистить", command=self.on_test_clear).grid(row=4, column=1, **pad)

        ttk.Label(test_frame, text="Скан от/до:").grid(row=5, column=0, sticky="e", **pad)
        self.scan_from_var = tk.StringVar(value="1")
        self.scan_to_var = tk.StringVar(value="40")
        ttk.Entry(test_frame, textvariable=self.scan_from_var, width=6).grid(row=5, column=1, sticky="w", **pad)
        ttk.Entry(test_frame, textvariable=self.scan_to_var, width=6).grid(row=5, column=1, sticky="e", **pad)

        ttk.Label(test_frame, text="Пауза (с):").grid(row=6, column=0, sticky="e", **pad)
        self.scan_delay_var = tk.StringVar(value="0.15")
        ttk.Entry(test_frame, textvariable=self.scan_delay_var, width=14).grid(row=6, column=1, sticky="w", **pad)
        self.scan_clear_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(test_frame, text="Гасить предыдущий адрес", variable=self.scan_clear_var).grid(row=6, column=2, sticky="w", **pad)
        self.scan_start_btn = ttk.Button(test_frame, text="Старт скан", command=self.on_scan_start)
        self.scan_start_btn.grid(row=7, column=0, **pad)
        self.scan_stop_btn = ttk.Button(test_frame, text="Стоп скан", command=self.on_scan_stop)
        self.scan_stop_btn.grid(row=7, column=1, **pad)

        ttk.Label(test_frame, text="Смена адреса:").grid(row=8, column=0, sticky="e", **pad)
        self.old_addr_var = tk.StringVar(value="1")
        self.new_addr_var = tk.StringVar(value="1")
        ttk.Entry(test_frame, textvariable=self.old_addr_var, width=6).grid(row=8, column=1, sticky="w", **pad)
        ttk.Entry(test_frame, textvariable=self.new_addr_var, width=6).grid(row=8, column=1, sticky="e", **pad)
        self.change_addr_btn = ttk.Button(test_frame, text="Применить", command=self.on_change_addr)
        self.change_addr_btn.grid(row=8, column=2, **pad)

        ttk.Label(test_frame, text=f"Карта: {self.map_path}").grid(row=9, column=0, columnspan=2, sticky="w", **pad)
        ttk.Button(test_frame, text="Перезагрузить", command=self._load_map).grid(row=9, column=2, **pad)

        self.status_var = tk.StringVar(value="Ready.")
        ttk.Label(frm, textvariable=self.status_var).grid(row=1, column=0, columnspan=3, sticky="w", **pad)

        self.status_var = tk.StringVar(value="Ready.")
        ttk.Label(frm, textvariable=self.status_var).grid(row=1, column=0, columnspan=3, sticky="w", **pad)

        self.status_var = tk.StringVar(value="Ready.")
        ttk.Label(frm, textvariable=self.status_var).grid(row=1, column=0, columnspan=3, sticky="w", **pad)


    def _refresh_ports(self):
        ports = [p.device for p in serial.tools.list_ports.comports()]
        if not ports:
            ports = ["COM3"]
        self.port_combo["values"] = ports
        if self.port_var.get() not in ports:
            self.port_var.set(ports[0])

    def _get_map_path(self):
        base = os.path.dirname(sys.argv[0] if getattr(sys, "frozen", False) else __file__)
        return os.path.join(base, "tablo_map.ini")

    def _get_settings_path(self):
        base = os.path.dirname(sys.argv[0] if getattr(sys, "frozen", False) else __file__)
        return os.path.join(base, "tablo_settings.ini")

    def _cred_read(self, target):
        try:
            advapi = ctypes.WinDLL("advapi32", use_last_error=True)
            CredReadW = advapi.CredReadW
            CredReadW.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.POINTER(ctypes.c_void_p)]
            CredReadW.restype = wintypes.BOOL
            CredFree = advapi.CredFree
            CredFree.argtypes = [ctypes.c_void_p]
            CredFree.restype = None

            pcred = ctypes.c_void_p()
            if not CredReadW(target, 1, 0, ctypes.byref(pcred)):
                return None

            class CREDENTIAL(ctypes.Structure):
                _fields_ = [
                    ("Flags", wintypes.DWORD),
                    ("Type", wintypes.DWORD),
                    ("TargetName", wintypes.LPWSTR),
                    ("Comment", wintypes.LPWSTR),
                    ("LastWritten", wintypes.FILETIME),
                    ("CredentialBlobSize", wintypes.DWORD),
                    ("CredentialBlob", ctypes.POINTER(ctypes.c_byte)),
                    ("Persist", wintypes.DWORD),
                    ("AttributeCount", wintypes.DWORD),
                    ("Attributes", ctypes.c_void_p),
                    ("TargetAlias", wintypes.LPWSTR),
                    ("UserName", wintypes.LPWSTR),
                ]

            cred = ctypes.cast(pcred, ctypes.POINTER(CREDENTIAL)).contents
            blob = ctypes.string_at(cred.CredentialBlob, cred.CredentialBlobSize)
            CredFree(pcred)
            return blob.decode("utf-16-le", errors="ignore")
        except Exception:
            return None

    def _cred_write(self, target, secret):
        try:
            advapi = ctypes.WinDLL("advapi32", use_last_error=True)
            CredWriteW = advapi.CredWriteW
            CredWriteW.argtypes = [ctypes.c_void_p, wintypes.DWORD]
            CredWriteW.restype = wintypes.BOOL

            class CREDENTIAL(ctypes.Structure):
                _fields_ = [
                    ("Flags", wintypes.DWORD),
                    ("Type", wintypes.DWORD),
                    ("TargetName", wintypes.LPWSTR),
                    ("Comment", wintypes.LPWSTR),
                    ("LastWritten", wintypes.FILETIME),
                    ("CredentialBlobSize", wintypes.DWORD),
                    ("CredentialBlob", ctypes.POINTER(ctypes.c_byte)),
                    ("Persist", wintypes.DWORD),
                    ("AttributeCount", wintypes.DWORD),
                    ("Attributes", ctypes.c_void_p),
                    ("TargetAlias", wintypes.LPWSTR),
                    ("UserName", wintypes.LPWSTR),
                ]

            blob = secret.encode("utf-16-le")
            credential = CREDENTIAL()
            credential.Flags = 0
            credential.Type = 1  # CRED_TYPE_GENERIC
            credential.TargetName = target
            credential.Comment = None
            credential.CredentialBlobSize = len(blob)
            credential.CredentialBlob = ctypes.cast(ctypes.create_string_buffer(blob), ctypes.POINTER(ctypes.c_byte))
            credential.Persist = 2  # CRED_PERSIST_LOCAL_MACHINE
            credential.AttributeCount = 0
            credential.Attributes = None
            credential.TargetAlias = None
            credential.UserName = "tablo_tool"

            if not CredWriteW(ctypes.byref(credential), 0):
                return False
            return True
        except Exception:
            return False

    def _load_settings(self):
        if not os.path.exists(self.settings_path):
            # still try to read password from Credential Manager
            saved = self._cred_read(self._cred_target)
            if saved:
                self.db_pass_var.set(saved)
            return
        cfg = configparser.ConfigParser()
        cfg.read(self.settings_path, encoding="utf-8")
        if "db" in cfg:
            self.db_host_var.set(cfg["db"].get("host", self.db_host_var.get()))
            self.db_port_var.set(cfg["db"].get("port", self.db_port_var.get()))
            self.db_user_var.set(cfg["db"].get("user", self.db_user_var.get()))
            # password is stored in Windows Credential Manager
            self.db_name_var.set(cfg["db"].get("database", self.db_name_var.get()))
        saved = self._cred_read(self._cred_target)
        if saved:
            self.db_pass_var.set(saved)
        if "app" in cfg:
            self.process_existing_var.set(cfg["app"].getboolean("process_existing", False))
            self.db_poll_var.set(cfg["app"].get("poll", self.db_poll_var.get()))
            self.port_var.set(cfg["app"].get("com_port", self.port_var.get()))
            protocol_id = cfg["app"].get("protocol", PROTOCOL_RS485)
            self.protocol_label_var.set(PROTOCOL_LABEL_BY_ID.get(protocol_id, PROTOCOL_LABEL_BY_ID[PROTOCOL_RS485]))

    def _save_settings(self):
        cfg = configparser.ConfigParser()
        cfg["db"] = {
            "host": self.db_host_var.get(),
            "port": self.db_port_var.get(),
            "user": self.db_user_var.get(),
            "database": self.db_name_var.get(),
        }
        cfg["app"] = {
            "process_existing": str(self.process_existing_var.get()),
            "poll": self.db_poll_var.get(),
            "com_port": self.port_var.get(),
            "protocol": self._protocol_id(),
        }
        with open(self.settings_path, "w", encoding="utf-8") as f:
            cfg.write(f)
        if self.db_pass_var.get():
            self._cred_write(self._cred_target, self.db_pass_var.get())

    def _load_map(self):
        self.addr_map = {}
        if not os.path.exists(self.map_path):
            try:
                cfg = configparser.ConfigParser()
                cfg["map"] = {"1": "1"}
                with open(self.map_path, "w", encoding="utf-8") as f:
                    cfg.write(f)
                self.status_var.set("Map created (tablo_map.ini).")
            except Exception:
                self.status_var.set("Map not found, using cabinet_id directly.")
            return
        cfg = configparser.ConfigParser()
        cfg.read(self.map_path, encoding="utf-8")
        if "map" not in cfg:
            self.status_var.set("Map section missing, using cabinet_id directly.")
            return
        for k, v in cfg["map"].items():
            try:
                cab = int(k.strip())
                addr = int(v.strip())
                if cab > 0:
                    self.addr_map[cab] = addr
            except Exception:
                continue
        self.status_var.set(f"Map loaded: {len(self.addr_map)} entries.")

    def _protocol_id(self):
        return PROTOCOL_LABELS.get(self.protocol_label_var.get(), PROTOCOL_RS485)

    def _update_protocol_ui(self):
        if self._protocol_id() == PROTOCOL_RS485:
            self.test_value_label.configure(text="Текст (4 симв.):")
            self.change_addr_btn.state(["!disabled"])
            if not self.test_text_var.get() or self.test_text_var.get().isdigit():
                self.test_text_var.set((self.test_text_var.get() or "1").zfill(4)[-4:])
        else:
            self.test_value_label.configure(text="Номер (0..999):")
            self.change_addr_btn.state(["disabled"])
            current = "".join(ch for ch in self.test_text_var.get() if ch.isdigit()) or "1"
            self.test_text_var.set(str(int(current)))

    def on_db_start(self):
        if self._db_thread and self._db_thread.is_alive():
            return
        if pymysql is None:
            messagebox.showerror("Error", "pymysql is not installed. Install it first.")
            return
        try:
            if not self.db_user_var.get() or not self.db_name_var.get():
                raise ValueError("Заполните Пользователь и База")
            poll = float(self.db_poll_var.get())
            if poll < 0.1:
                raise ValueError("Poll must be >= 0.1 seconds")
            self._save_settings()
            self._db_stop.clear()
            self._db_thread = threading.Thread(target=self._db_worker, daemon=True)
            self._db_thread.start()
            self.status_var.set("DB мониторинг запущен.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def on_db_stop(self):
        self._db_stop.set()
        self.status_var.set("DB мониторинг остановлен.")

    def _db_connect(self):
        return pymysql.connect(
            host=self.db_host_var.get(),
            port=int(self.db_port_var.get()),
            user=self.db_user_var.get(),
            password=self.db_pass_var.get(),
            database=self.db_name_var.get(),
            charset="utf8",
            autocommit=True,
        )

    def _db_worker(self):
        # Read-only monitor: only SELECT queries
        addr_field = self.addr_by_var.get()
        text_mode = self.text_mode_var.get()
        poll = float(self.db_poll_var.get())

        def make_text(prefix, queue_num):
            if text_mode == "prefix+3" and prefix:
                return f"{prefix}{int(queue_num):03d}"
            return f"{int(queue_num):04d}"

        while not self._db_stop.is_set():
            try:
                with self._db_connect() as conn:
                    with conn.cursor() as cur:
                        # Build operator mapping: orders_list.oper_id -> operators.id
                        cur.execute("SELECT id, operator_id FROM operators")
                        op_map = {int(op_id): int(op_db_id) for op_db_id, op_id in cur.fetchall()}

                        # Initialize last id if needed
                        if self._last_orders_id == 0 and not self.process_existing_var.get():
                            cur.execute("SELECT IFNULL(MAX(id),0) FROM orders_list")
                            self._last_orders_id = int(cur.fetchone()[0])

                        # Fetch new orders
                        cur.execute(
                            "SELECT id, oper_id, queue_num, prefix, zone_id, cabinet_id, room_id "
                            "FROM orders_list WHERE id > %s ORDER BY id ASC",
                            (self._last_orders_id,),
                        )
                        rows = cur.fetchall()
                        for row in rows:
                            order_id, oper_id, queue_num, prefix, zone_id, cabinet_id, room_id = row
                        rows = cur.fetchall()
                        for row in rows:
                            order_id, oper_id, queue_num, prefix, zone_id, cabinet_id, room_id = row
                            self._last_orders_id = max(self._last_orders_id, int(order_id))

                            operator_db_id = op_map.get(int(oper_id))
                            if operator_db_id is None:
                                continue
                            addr_source = {
                                "zone_id": zone_id,
                                "cabinet_id": cabinet_id,
                                "room_id": room_id,
                                "oper_id": oper_id,
                            }.get(addr_field, zone_id)
                            if addr_field == "cabinet_id" and cabinet_id:
                                addr_source = self.addr_map.get(int(cabinet_id), int(cabinet_id))
                            if addr_source is None:
                                continue

                            text = make_text(prefix, queue_num)
                            try:
                                display_value = text if self._protocol_id() == PROTOCOL_RS485 else int(queue_num)
                                self._send_display(int(addr_source), display_value, False)
                                self._db_active[(operator_db_id, int(queue_num))] = {
                                    "addr": int(addr_source),
                                    "text": text,
                                }
                            except Exception:
                                pass

                        if self._db_active:
                            for (operator_db_id, queue_num), info in list(self._db_active.items()):
                                cur.execute(
                                    "SELECT finished, cancelled FROM queue "
                                    "WHERE operator_id=%s AND queue_num=%s "
                                    "ORDER BY id DESC LIMIT 1",
                                    (operator_db_id, queue_num),
                                )
                                row = cur.fetchone()
                                if not row:
                                    continue
                                finished, cancelled = row
                                if int(finished) == 1 or int(cancelled) == 1:
                                    try:
                                        self._send_clear(int(info["addr"]))
                                    except Exception:
                                        pass
                                    self._db_active.pop((operator_db_id, queue_num), None)

                self.status_var.set(f"DB активные: {len(self._db_active)}")
            except Exception:
                self.status_var.set("DB error (read-only)")
            time.sleep(poll)

    def _require_rs485_addr(self, addr: int):
        if not (0 < addr < 255) or addr == DELIMITER:
            raise ValueError("Для RS-485 адрес должен быть 1..254 и не 240")

    def _require_rek_window(self, addr: int):
        if not (0 <= addr <= 99):
            raise ValueError("Для COM табло (rek) номер окна должен быть в диапазоне 0..99")

    def _parse_test_addr(self) -> int:
        addr = int(self.test_addr_var.get())
        if self._protocol_id() == PROTOCOL_RS485:
            self._require_rs485_addr(addr)
        else:
            self._require_rek_window(addr)
        return addr

    def _normalize_rs485_text(self, value: str) -> str:
        value = value.strip()
        if len(value) != 4:
            raise ValueError("Для RS-485 текст должен быть ровно из 4 символов")
        return value

    def _normalize_rek_number(self, value) -> int:
        text = str(value).strip()
        if not text:
            raise ValueError("Укажите номер для COM табло (rek)")
        number = int(text)
        if not (0 <= number <= 999):
            raise ValueError("Для COM табло (rek) номер должен быть в диапазоне 0..999")
        return number

    def _send_display(self, addr: int, value, blink: bool = False):
        if self._protocol_id() == PROTOCOL_RS485:
            rs485_send(self.port_var.get(), build_rs485_frame(addr, self._normalize_rs485_text(str(value)), blink))
            return
        rek_com_send(self.port_var.get(), build_rek_com_frame(addr, self._normalize_rek_number(value)))

    def _send_clear(self, addr: int):
        if self._protocol_id() == PROTOCOL_RS485:
            rs485_send(self.port_var.get(), build_rs485_blank(addr))
            return
        rek_com_send(self.port_var.get(), build_rek_com_clear(addr))

    def on_test_send(self):
        try:
            addr = self._parse_test_addr()
            value = self.test_text_var.get()
            if self._protocol_id() == PROTOCOL_RS485:
                value = self._normalize_rs485_text(value)
            else:
                value = self._normalize_rek_number(value)
            self._send_display(addr, value, self.test_blink_var.get())
            self.status_var.set(f"Тест отправлен на адрес {addr}.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def on_test_clear(self):
        try:
            addr = self._parse_test_addr()
            self._send_clear(addr)
            self.status_var.set(f"Тест очищен для адреса {addr}.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def on_change_addr(self):
        try:
            if self._protocol_id() != PROTOCOL_RS485:
                raise ValueError("Смена адреса поддерживается только для RS-485 режима")
            old_addr = int(self.old_addr_var.get())
            new_addr = int(self.new_addr_var.get())
            self._require_rs485_addr(old_addr)
            self._require_rs485_addr(new_addr)
            rs485_send(self.port_var.get(), build_rs485_change_addr(old_addr, new_addr))
            self.status_var.set(f"Адрес изменён: {old_addr} -> {new_addr}.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def on_scan_start(self):
        if self._scan_thread and self._scan_thread.is_alive():
            return
        try:
            start = int(self.scan_from_var.get())
            end = int(self.scan_to_var.get())
            delay = float(self.scan_delay_var.get())
            if self._protocol_id() == PROTOCOL_RS485:
                if start < 1 or end > 254 or start > end:
                    raise ValueError("Диапазон RS-485 должен быть в пределах 1..254")
            else:
                if start < 0 or end > 99 or start > end:
                    raise ValueError("Диапазон номеров окон должен быть в пределах 0..99")
                self._normalize_rek_number(self.test_text_var.get())
            if delay < 0.05:
                raise ValueError("Пауза должна быть не меньше 0.05 сек")
            self._scan_stop.clear()
            self._scan_thread = threading.Thread(target=self._scan_worker, args=(start, end, delay), daemon=True)
            self._scan_thread.start()
            self.status_var.set("Сканирование запущено.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def on_scan_stop(self):
        self._scan_stop.set()
        self.status_var.set("Сканирование остановлено.")

    def _scan_worker(self, start: int, end: int, delay: float):
        protocol_id = self._protocol_id()
        port = self.port_var.get()
        blink = self.test_blink_var.get()
        auto_clear = self.scan_clear_var.get()
        last_addr = None
        text = self._normalize_rs485_text(self.test_text_var.get().zfill(4)[-4:]) if protocol_id == PROTOCOL_RS485 else None
        number = None if protocol_id == PROTOCOL_RS485 else self._normalize_rek_number(self.test_text_var.get())
        for addr in range(start, end + 1):
            if self._scan_stop.is_set():
                if protocol_id == PROTOCOL_REK_COM and auto_clear and last_addr is not None:
                    try:
                        rek_com_send(port, build_rek_com_clear(last_addr), repeat=1)
                    except Exception:
                        pass
                return
            try:
                if protocol_id == PROTOCOL_RS485:
                    rs485_send(port, build_rs485_frame(addr, text, blink))
                else:
                    if auto_clear and last_addr is not None:
                        rek_com_send(port, build_rek_com_clear(last_addr), repeat=1)
                        time.sleep(0.05)
                    rek_com_send(port, build_rek_com_frame(addr, number), repeat=1)
                    last_addr = addr
                self.status_var.set(f"Проверяю адрес {addr}.")
            except Exception:
                self.status_var.set("Ошибка сканирования.")
                return
            time.sleep(delay)
        if protocol_id == PROTOCOL_REK_COM and auto_clear and last_addr is not None:
            try:
                rek_com_send(port, build_rek_com_clear(last_addr), repeat=1)
            except Exception:
                pass
        self.status_var.set("Сканирование завершено.")

    def _all_known_addresses(self):
        addrs = set()
        for v in self.addr_map.values():
            try:
                v = int(v)
                if self._protocol_id() == PROTOCOL_RS485:
                    if 0 < v < 255 and v != DELIMITER:
                        addrs.add(v)
                elif 0 <= v <= 99:
                    addrs.add(v)
            except Exception:
                pass
        for info in self._db_active.values():
            try:
                addrs.add(int(info.get("addr")))
            except Exception:
                pass
        return sorted(addrs)
    def _shutdown_clear_all(self):
        try:
            port = self.port_var.get()
            for addr in self._all_known_addresses():
                if self._protocol_id() == PROTOCOL_RS485:
                    rs485_send(port, build_rs485_blank(addr))
                else:
                    rek_com_send(port, build_rek_com_clear(addr), repeat=1)
        except Exception:
            pass

    def on_exit(self):
        self._db_stop.set()
        self._scan_stop.set()
        try:
            self._save_settings()
        except Exception:
            pass
        self._shutdown_clear_all()
        if self._tray:
            try:
                self._tray.stop()
            except Exception:
                pass
        self.destroy()

    def _create_tray_image(self):
        if Image is None or ImageDraw is None:
            return None
        img = Image.new("RGB", (64, 64), "#F4F1EC")
        d = ImageDraw.Draw(img)
        d.rectangle((8, 10, 56, 54), outline="#2E2A25", width=3)
        d.text((16, 24), "TB", fill="#2E2A25")
        return img

    def _hide_to_tray(self):
        if pystray is None:
            # Fallback: just minimize
            self.iconify()
            return
        if self._tray is not None:
            self.withdraw()
            return

        def on_show(icon, item):
            self.after(0, self._restore_from_tray)

        def on_exit(icon, item):
            self.after(0, self.on_exit)

        icon_image = self._create_tray_image()
        menu = pystray.Menu(
            pystray.MenuItem("Показать", on_show),
            pystray.MenuItem("Выход", on_exit),
        )
        self._tray = pystray.Icon("tablo_tool", icon_image, "Tablo", menu)

        def _run_tray():
            try:
                self._tray.run()
            except Exception:
                pass

        self._tray_thread = threading.Thread(target=_run_tray, daemon=True)
        self._tray_thread.start()
        self.withdraw()

    def _restore_from_tray(self):
        self.deiconify()
        self.lift()
        self.focus_force()


if __name__ == "__main__":
    App().mainloop()
