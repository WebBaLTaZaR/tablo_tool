import configparser
import os
import sys
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox

import serial
import serial.tools.list_ports

try:
    import pymysql
except Exception:
    pymysql = None


DELIMITER = 0xF0
DEFAULT_BAUD = 9600
REPEAT_COUNT = 7


def build_frame(addr: int, text: str, blink: bool) -> bytes:
    if len(text) != 4:
        raise ValueError("Text must be exactly 4 characters")
    blink_byte = 10 if blink else 0
    payload = [DELIMITER, 0, addr, blink_byte] + [ord(c) for c in text]
    return bytes(payload)


def build_blank(addr: int) -> bytes:
    return bytes([DELIMITER, 0, addr, 15, 32, 32, 32, 32])


def build_change_addr(old_addr: int, new_addr: int) -> bytes:
    return bytes([DELIMITER, 255, old_addr, old_addr, old_addr, new_addr, new_addr, new_addr])


def send_bytes(port: str, data: bytes, baud: int = DEFAULT_BAUD):
    ser = None
    try:
        ser = serial.Serial(port, baud)
        ser.write(data * REPEAT_COUNT)
        ser.flush()
        time.sleep(1.0)
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

        self._apply_theme()
        self._build_ui()
        self._refresh_ports()
        self._load_map()

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

        ttk.Label(db_frame, text="COM-порт:").grid(row=1, column=0, sticky="e", **pad)
        self.port_var = tk.StringVar(value="COM3")
        self.port_combo = ttk.Combobox(db_frame, textvariable=self.port_var, width=12)
        self.port_combo.grid(row=1, column=1, sticky="w", **pad)
        ttk.Button(db_frame, text="Обновить", command=self._refresh_ports).grid(row=1, column=2, **pad)

        sep1 = ttk.Separator(db_frame, orient="horizontal")
        sep1.grid(row=2, column=0, columnspan=3, sticky="ew", padx=8, pady=6)

        ttk.Label(db_frame, text="База данных", style="Header.TLabel").grid(
            row=3, column=0, columnspan=3, sticky="w", padx=8, pady=(2, 6)
        )

        ttk.Label(db_frame, text="Хост:").grid(row=4, column=0, sticky="e", **pad)
        self.db_host_var = tk.StringVar(value="localhost")
        ttk.Entry(db_frame, textvariable=self.db_host_var, width=14).grid(row=4, column=1, sticky="w", **pad)

        ttk.Label(db_frame, text="Порт:").grid(row=5, column=0, sticky="e", **pad)
        self.db_port_var = tk.StringVar(value="3306")
        ttk.Entry(db_frame, textvariable=self.db_port_var, width=14).grid(row=5, column=1, sticky="w", **pad)

        ttk.Label(db_frame, text="Пользователь:").grid(row=6, column=0, sticky="e", **pad)
        self.db_user_var = tk.StringVar(value="")
        ttk.Entry(db_frame, textvariable=self.db_user_var, width=14).grid(row=6, column=1, sticky="w", **pad)

        ttk.Label(db_frame, text="Пароль:").grid(row=7, column=0, sticky="e", **pad)
        self.db_pass_var = tk.StringVar(value="")
        ttk.Entry(db_frame, textvariable=self.db_pass_var, width=14, show="*").grid(row=7, column=1, sticky="w", **pad)

        ttk.Label(db_frame, text="База:").grid(row=8, column=0, sticky="e", **pad)
        self.db_name_var = tk.StringVar(value="")
        ttk.Entry(db_frame, textvariable=self.db_name_var, width=14).grid(row=8, column=1, sticky="w", **pad)

        self.process_existing_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(db_frame, text="Обработать уже существующие", variable=self.process_existing_var).grid(
            row=9, column=1, sticky="w", **pad
        )

        ttk.Label(db_frame, text="Интервал (с):").grid(row=10, column=0, sticky="e", **pad)
        self.db_poll_var = tk.StringVar(value="0.5")
        ttk.Entry(db_frame, textvariable=self.db_poll_var, width=14).grid(row=10, column=1, sticky="w", **pad)

        ttk.Button(db_frame, text="Старт", style="Primary.TButton", command=self.on_db_start).grid(
            row=11, column=0, **pad
        )
        ttk.Button(db_frame, text="Стоп", command=self.on_db_stop).grid(row=11, column=1, **pad)

        ttk.Label(test_frame, text="Инструменты", style="Header.TLabel").grid(
            row=0, column=0, columnspan=3, sticky="w", padx=8, pady=(2, 6)
        )

        ttk.Label(test_frame, text="Адрес:").grid(row=1, column=0, sticky="e", **pad)
        self.test_addr_var = tk.StringVar(value="1")
        ttk.Entry(test_frame, textvariable=self.test_addr_var, width=14).grid(row=1, column=1, sticky="w", **pad)

        ttk.Label(test_frame, text="Текст (4 симв.):").grid(row=2, column=0, sticky="e", **pad)
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

        ttk.Button(test_frame, text="Старт скан", command=self.on_scan_start).grid(row=7, column=0, **pad)
        ttk.Button(test_frame, text="Стоп скан", command=self.on_scan_stop).grid(row=7, column=1, **pad)

        ttk.Label(test_frame, text="Смена адреса:").grid(row=8, column=0, sticky="e", **pad)
        self.old_addr_var = tk.StringVar(value="1")
        self.new_addr_var = tk.StringVar(value="1")
        ttk.Entry(test_frame, textvariable=self.old_addr_var, width=6).grid(row=8, column=1, sticky="w", **pad)
        ttk.Entry(test_frame, textvariable=self.new_addr_var, width=6).grid(row=8, column=1, sticky="e", **pad)
        ttk.Button(test_frame, text="Применить", command=self.on_change_addr).grid(row=8, column=2, **pad)

        ttk.Label(test_frame, text=f"Карта: {self.map_path}").grid(row=9, column=0, columnspan=2, sticky="w", **pad)
        ttk.Button(test_frame, text="Перезагрузить", command=self._load_map).grid(row=9, column=2, **pad)

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
                if 0 < addr < 255 and addr != DELIMITER:
                    self.addr_map[cab] = addr
            except Exception:
                continue
        self.status_var.set(f"Map loaded: {len(self.addr_map)} entries.")

    def on_db_start(self):
        if self._db_thread and self._db_thread.is_alive():
            return
        if pymysql is None:
            messagebox.showerror("Error", "pymysql is not installed. Install it first.")
            return
        try:
            poll = float(self.db_poll_var.get())
            if poll < 0.1:
                raise ValueError("Poll must be >= 0.1 seconds")
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
                            if not addr_source:
                                continue

                            text = make_text(prefix, queue_num)
                            try:
                                frame = build_frame(int(addr_source), text, False)
                                send_bytes(self.port_var.get(), frame)
                                self._db_active[(operator_db_id, int(queue_num))] = {
                                    "addr": int(addr_source),
                                    "text": text,
                                }
                            except Exception:
                                pass

                        # Check for finished/cancelled
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
                                        frame = build_blank(int(info["addr"]))
                                        send_bytes(self.port_var.get(), frame)
                                    except Exception:
                                        pass
                                    self._db_active.pop((operator_db_id, queue_num), None)

                self.status_var.set(f"DB активные: {len(self._db_active)}")
            except Exception:
                self.status_var.set("DB error (read-only)")
            time.sleep(poll)

    def _parse_test_addr(self) -> int:
        addr = int(self.test_addr_var.get())
        if not (0 < addr < 255) or addr == DELIMITER:
            raise ValueError("Address must be 1..254 and not 240")
        return addr

    def on_test_send(self):
        try:
            addr = self._parse_test_addr()
            text = self.test_text_var.get()
            frame = build_frame(addr, text, self.test_blink_var.get())
            send_bytes(self.port_var.get(), frame)
            self.status_var.set(f"Test sent to addr {addr}.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def on_test_clear(self):
        try:
            addr = self._parse_test_addr()
            frame = build_blank(addr)
            send_bytes(self.port_var.get(), frame)
            self.status_var.set(f"Test cleared addr {addr}.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def on_change_addr(self):
        try:
            old_addr = int(self.old_addr_var.get())
            new_addr = int(self.new_addr_var.get())
            for a in (old_addr, new_addr):
                if not (0 < a < 255) or a == DELIMITER:
                    raise ValueError("Address must be 1..254 and not 240")
            frame = build_change_addr(old_addr, new_addr)
            send_bytes(self.port_var.get(), frame)
            self.status_var.set(f"Addr changed {old_addr} -> {new_addr}.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def on_scan_start(self):
        if self._scan_thread and self._scan_thread.is_alive():
            return
        try:
            start = int(self.scan_from_var.get())
            end = int(self.scan_to_var.get())
            delay = float(self.scan_delay_var.get())
            if start < 1 or end > 254 or start > end:
                raise ValueError("Scan range must be within 1..254")
            self._scan_stop.clear()
            self._scan_thread = threading.Thread(
                target=self._scan_worker, args=(start, end, delay), daemon=True
            )
            self._scan_thread.start()
            self.status_var.set("Scanning...")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def on_scan_stop(self):
        self._scan_stop.set()
        self.status_var.set("Scan stopped.")

    def _scan_worker(self, start: int, end: int, delay: float):
        port = self.port_var.get()
        text = self.test_text_var.get()
        blink = self.test_blink_var.get()
        for addr in range(start, end + 1):
            if self._scan_stop.is_set():
                return
            try:
                frame = build_frame(addr, text, blink)
                send_bytes(port, frame)
                self.status_var.set(f"Sent to addr {addr}.")
            except Exception:
                self.status_var.set("Serial error.")
                return
            time.sleep(delay)


if __name__ == "__main__":
    App().mainloop()
