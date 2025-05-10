import logging
from logging.handlers import RotatingFileHandler
from concurrent.futures import ThreadPoolExecutor, as_completed
from cachetools import TTLCache
import os
import sys
import psutil
import hashlib
import shutil
import threading
import json
import time
from tkinter import *
from tkinter import ttk, filedialog, messagebox, scrolledtext
import tkinter as tk
from queue import Queue, Empty
from datetime import datetime
from collections import deque
import schedule


class SecurityError(Exception):
    """Error personalizado para problemas de seguridad"""

    pass


class ThreadManager:
    """Gestor profesional de hilos con supervisión"""

    def __init__(self):
        self.threads = {}
        self.lock = threading.Lock()

    def add_thread(self, name, target, daemon=False):
        with self.lock:
            self.threads[name] = {
                "thread": threading.Thread(
                    target=self._thread_wrapper,
                    args=(name, target),
                    daemon=daemon,
                    name=name,
                ),
                "active": False,
                "target": target,
            }

    def _thread_wrapper(self, name, target):
        """Envuelve cada hilo para manejo de errores"""
        try:
            self.threads[name]["active"] = True
            target()
        except Exception as e:
            logging.error(f"Thread {name} crashed: {str(e)}", exc_info=True)
        finally:
            self.threads[name]["active"] = False

    def start_all(self):
        for thread_info in self.threads.values():
            thread_info["thread"].start()

    def stop_all(self, timeout=5):
        for name, thread_info in self.threads.items():
            if thread_info["thread"].is_alive():
                thread_info["thread"].join(timeout)
                if thread_info["thread"].is_alive():
                    logging.warning(f"Thread {name} didn't stop gracefully")


class ToolTip:
    """Implementación profesional de tooltips"""

    def __init__(self, widget, text, bg, fg, font):
        self.widget = widget
        self.text = text
        self.bg = bg
        self.fg = fg
        self.font = font
        self.tip_window = None
        self.id = None
        self.x = self.y = 0
        self.widget.bind("<Enter>", self.show)
        self.widget.bind("<Leave>", self.hide)

    def show(self, event=None):
        """Muestra el tooltip con formato profesional"""
        if self.tip_window or not self.text:
            return
        x, y, _, _ = self.widget.bbox("insert")
        x += self.widget.winfo_rootx() + 25
        y += self.widget.winfo_rooty() + 25

        self.tip_window = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{x}+{y}")

        label = tk.Label(
            tw,
            text=self.text,
            justify=tk.LEFT,
            background=self.bg,
            foreground=self.fg,
            relief=tk.SOLID,
            borderwidth=1,
            font=self.font,
            wraplength=200,
        )
        label.pack(ipadx=1)

    def hide(self, event=None):
        """Oculta el tooltip"""
        if self.tip_window:
            self.tip_window.destroy()
            self.tip_window = None


class FileOrganizerGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.setup_logging()  # Primero el logging
        self.logger.info("Inicializando aplicación")
        self.performance_cache = {
            "directory_scan": TTLCache(maxsize=100, ttl=30),
            "file_operations": TTLCache(maxsize=500, ttl=60),
        }
        self.setup_performance_optimizations()
        self.init_threads()
        self.create_widgets()
        self.title("Organizador Avanzado de Archivos")
        self.geometry("900x700")
        self.configure(bg="#f0f0f0")
        self.profiles = {}
        self.current_profile = "default"
        self.undo_stack = deque(maxlen=5)
        self.task_queue = Queue()
        self.running = True
        self.theme_mode = "light"

        # Inicializar configuración predeterminada
        self.default_formats = {
            ".jpg": "Fotos",
            ".png": "Fotos",
            ".ico": "Iconos",
            ".mp4": "Videos",
            ".avi": "Videos",
            ".mpg": "Videos",
            ".mp3": "Musica",
            ".pdf": "PDFs",
            ".docx": "Documentos_work",
            ".doc": "Documentos_work",
            ".txt": "Documentos_txt",
            "": "Otros",
        }

        self.init_threads()
        self.create_widgets()
        self.load_profiles()
        self.update_theme()

    def log(self, message):
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.log_area.insert(END, f"[{timestamp}] {message}\n")
        self.log_area.see(END)

    def select_directory(self):
        directory = filedialog.askdirectory(title="Seleccionar carpeta a organizar")
        if directory:  # Si el usuario no cancela
            self.dir_entry.delete(0, tk.END)
            self.dir_entry.insert(0, directory)

    def create_widgets(self):
        """Versión mejorada con UI profesional"""
        # Configuración de estilo avanzado
        self.style = ttk.Style()
        self.setup_theme_system()

        # Frame principal con mejor organización
        main_frame = ttk.Frame(self, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)

        # Sistema de pestañas
        self.notebook = ttk.Notebook(main_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        # Pestaña de operaciones
        ops_tab = ttk.Frame(self.notebook)
        self.build_operations_tab(ops_tab)
        self.notebook.add(ops_tab, text="Operaciones")

        # Pestaña de configuración
        config_tab = ttk.Frame(self.notebook)
        self.build_config_tab(config_tab)
        self.notebook.add(config_tab, text="Configuración")

        # Barra de estado profesional
        self.setup_status_bar(main_frame)

    def setup_theme_system(self):
        """Sistema completo de temas"""
        self.themes = {
            "light": {
                "primary": "#f0f0f0",
                "secondary": "#ffffff",
                "text": "#000000",
                "accent": "#0078d7",
            },
            "dark": {
                "primary": "#2d2d2d",
                "secondary": "#3d3d3d",
                "text": "#ffffff",
                "accent": "#0e639c",
            },
            "professional": {
                "primary": "#f5f5f5",
                "secondary": "#e0e0e0",
                "text": "#212121",
                "accent": "#607d8b",
            },
        }

        # Aplicar estilo a widgets
        for theme_name, colors in self.themes.items():
            self.style.theme_create(
                theme_name,
                parent="clam",
                settings={
                    "TFrame": {"configure": {"background": colors["primary"]}},
                    "TLabel": {
                        "configure": {
                            "background": colors["primary"],
                            "foreground": colors["text"],
                            "font": ("Segoe UI", 10),
                        }
                    },
                    # ... (configuraciones similares para otros widgets)
                },
            )

        self.style.theme_use("professional")

    def setup_status_bar(self, parent):
        """Barra de estado avanzada"""
        self.status_bar = ttk.Frame(parent)
        self.status_bar.pack(fill=tk.X, pady=(5, 0))

        # Componentes de la barra
        self.status_label = ttk.Label(
            self.status_bar, text="Listo", anchor=tk.W, style="Status.TLabel"
        )
        self.status_label.pack(side=tk.LEFT, fill=tk.X, expand=True)

        self.memory_usage = ttk.Label(self.status_bar, text="RAM: 0MB", anchor=tk.E)
        self.memory_usage.pack(side=tk.RIGHT)

        # Actualización periódica
        self.update_status_bar()

    def update_status_bar(self):
        """Actualiza dinámicamente la barra de estado"""
        # Uso de memoria
        process = psutil.Process(os.getpid())
        mem = process.memory_info().rss / 1024 / 1024
        self.memory_usage.config(text=f"RAM: {mem:.1f}MB")

        # Hilos activos
        threads = threading.active_count()

        # Tareas pendientes
        tasks = self.task_queue.qsize()

        self.status_label.config(
            text=f"Hilos: {threads} | Tareas: {tasks} | {datetime.now().strftime('%H:%M:%S')}"
        )

        self.after(1000, self.update_status_bar)

    def build_configuration_panel(self, parent):
        # Configuración de directorio
        dir_frame = ttk.LabelFrame(parent, text="Directorio")
        dir_frame.pack(padx=10, pady=5, fill=X)

        self.dir_entry = ttk.Entry(dir_frame)
        self.dir_entry.pack(side=LEFT, fill=X, expand=True, padx=5)

        ttk.Button(dir_frame, text="Examinar", command=self.select_directory).pack(
            side=LEFT
        )

        # Configuración de perfiles
        profile_frame = ttk.LabelFrame(parent, text="Perfiles")
        profile_frame.pack(padx=10, pady=5, fill=X)

        self.profile_combo = ttk.Combobox(profile_frame)
        self.profile_combo.pack(side=LEFT, fill=X, expand=True, padx=5)
        ttk.Button(profile_frame, text="Guardar", command=self.save_profile).pack(
            side=LEFT
        )
        ttk.Button(profile_frame, text="Eliminar", command=self.delete_profile).pack(
            side=LEFT
        )

        # Configuración de formatos
        format_frame = ttk.LabelFrame(parent, text="Formatos de Archivo")
        format_frame.pack(padx=10, pady=5, fill=BOTH, expand=True)

        self.search_entry = ttk.Entry(format_frame)
        self.search_entry.pack(fill=X, padx=5, pady=2)
        self.search_entry.bind("<KeyRelease>", self.filter_formats)

        self.format_tree = ttk.Treeview(
            format_frame, columns=("ext", "folder"), show="headings"
        )
        self.format_tree.heading("ext", text="Extensión")
        self.format_tree.heading("folder", text="Carpeta")
        self.format_tree.pack(fill=BOTH, expand=True)

        control_frame = ttk.Frame(format_frame)
        control_frame.pack(pady=5)
        ttk.Button(control_frame, text="Agregar", command=self.add_format).pack(
            side=LEFT
        )
        ttk.Button(control_frame, text="Eliminar", command=self.remove_format).pack(
            side=LEFT
        )

        # Configuración de programación
        schedule_frame = ttk.LabelFrame(parent, text="Programación")
        schedule_frame.pack(padx=10, pady=5, fill=X)

        self.schedule_combo = ttk.Combobox(
            schedule_frame, values=["Ninguna", "5 minutos", "1 hora", "Diario"]
        )
        self.schedule_combo.pack(side=LEFT, padx=5)
        ttk.Button(schedule_frame, text="Activar", command=self.enable_scheduling).pack(
            side=LEFT
        )

        # Barra de progreso
        self.progress = ttk.Progressbar(parent, orient=HORIZONTAL, mode="determinate")
        self.progress.pack(padx=10, pady=5, fill=X)

        # Controles principales
        control_frame = ttk.Frame(parent)
        control_frame.pack(pady=10)
        ttk.Button(
            control_frame, text="Previsualizar", command=self.preview_changes
        ).pack(side=LEFT, padx=5)
        ttk.Button(
            control_frame, text="Organizar Ahora", command=self.start_organization
        ).pack(side=LEFT, padx=5)
        ttk.Button(control_frame, text="Deshacer", command=self.undo_last).pack(
            side=LEFT, padx=5
        )
        ttk.Button(control_frame, text="Tema", command=self.toggle_theme).pack(
            side=LEFT, padx=5
        )

    def build_preview_panel(self, parent):
        # Área de previsualización
        preview_frame = ttk.LabelFrame(parent, text="Previsualización de Cambios")
        preview_frame.pack(padx=10, pady=5, fill=BOTH, expand=True)

        self.preview_tree = ttk.Treeview(
            preview_frame, columns=("original", "destino"), show="headings"
        )
        self.preview_tree.heading("original", text="Ubicación Original")
        self.preview_tree.heading("destino", text="Nueva Ubicación")
        self.preview_tree.pack(fill=BOTH, expand=True, side=LEFT)

        scrollbar = ttk.Scrollbar(
            preview_frame, orient=VERTICAL, command=self.preview_tree.yview
        )
        scrollbar.pack(side=RIGHT, fill=Y)
        self.preview_tree.configure(yscrollcommand=scrollbar.set)

        # Área de registro
        log_frame = ttk.LabelFrame(parent, text="Registro de Actividades")
        log_frame.pack(padx=10, pady=5, fill=BOTH, expand=True)

        self.log_area = scrolledtext.ScrolledText(log_frame, wrap=WORD)
        self.log_area.pack(fill=BOTH, expand=True)

    def filter_formats(self, event=None):
        query = self.search_entry.get().lower()
        all_items = [
            (child, self.format_tree.item(child)["values"])
            for child in self.format_tree.get_children()
        ]

        self.format_tree.delete(*self.format_tree.get_children())  # Limpiar todo

        for child, (ext, folder) in all_items:
            if query in ext.lower() or query in folder.lower():
                self.format_tree.insert("", "end", id=child, values=(ext, folder))

    def toggle_theme(self):
        self.theme_mode = "dark" if self.theme_mode == "light" else "light"
        self.update_theme()

    def update_theme(self):
        bg = "#333333" if self.theme_mode == "dark" else "#f0f0f0"
        fg = "#ffffff" if self.theme_mode == "dark" else "#000000"
        self.configure(background=bg)
        self.style.configure(".", background=bg, foreground=fg)
        self.log_area.configure(bg=bg, fg=fg, insertbackground=fg)

    def optimize_performance(self):
        """Aplicar optimizaciones de rendimiento correctamente"""
        # Cache para operaciones frecuentes
        self.ext_cache = TTLCache(maxsize=500, ttl=300)  # 5 minutos de cache
        self.folder_cache = TTLCache(maxsize=100, ttl=600)  # 10 minutos

        # Configuración CORRECTA de Treeview mediante estilos
        self.style.configure(
            "Treeview",
            font=("Segoe UI", 9),
            rowheight=25,
            borderwidth=1,
            relief="solid",
        )

        self.style.configure(
            "Treeview.Heading", font=("Segoe UI", 9, "bold"), padding=(5, 2, 5, 2)
        )

        # Configuración específica para cada treeview
        self.format_tree.configure(style="Custom.Treeview")
        self.preview_tree.configure(style="Custom.Treeview")

        # Crear un estilo personalizado si necesitas diferencias
        self.style.map(
            "Custom.Treeview",
            background=[("selected", "#0078d7")],
            foreground=[("selected", "white")],
        )

        # Manejo de actualizaciones
        self.tree_update_lock = threading.Lock()
        self.format_tree.bind("<<TreeviewOpen>>", self.on_treeview_update)
        self.preview_tree.bind("<<TreeviewOpen>>", self.on_treeview_update)

        # Precarga de iconos (versión mejorada)
        self.icon_cache = {}
        self.load_icons_async()

    def load_icons_async(self):
        """Carga los íconos en segundo plano para no bloquear la UI"""

        def _load_icons():
            icon_names = ["file", "folder", "image", "document", "audio"]
            for name in icon_names:
                try:
                    self.icon_cache[name] = tk.PhotoImage(file=f"icons/{name}.png")
                except Exception as e:
                    self.logger.warning(f"No se pudo cargar ícono {name}: {e}")

        threading.Thread(target=_load_icons, daemon=True, name="IconLoader").start()

    def on_treeview_update(self, event):
        """Maneja actualizaciones eficientes del Treeview"""
        with self.tree_update_lock:
            widget = event.widget
            widget.update_idletasks()

            # Limitar la frecuencia de actualización
            current_time = time.time()
            if hasattr(widget, "_last_update"):
                if current_time - widget._last_update < 0.1:  # 100ms
                    return
            widget._last_update = current_time

            # Actualización optimizada
            widget.see(event.widget.focus())

    def load_icons(self):
        """Precarga iconos para mejor rendimiento visual"""
        self.icons = {
            "file": tk.PhotoImage(file="icons/file.png"),
            "folder": tk.PhotoImage(file="icons/folder.png"),
            "image": tk.PhotoImage(file="icons/image.png"),
            "video": tk.PhotoImage(file="icons/video.png"),
        }
        for item in self.format_tree.get_children():
            ext = self.format_tree.item(item)["values"][0]
            icon = self.get_icon_for_extension(ext)
            self.format_tree.item(item, image=icon)

    def enhance_ui(self):
        """Mejoras visuales profesionales"""
        # Configuración de estilo avanzado
        self.style = ttk.Style()
        self.style.theme_use("clam")

        # Paleta de colores profesional
        self.setup_colors()

        # Tooltips avanzados
        self.setup_tooltips()

        # Animaciones fluidas
        self.setup_animations()

        # Barra de estado profesional
        self.setup_statusbar()

    def setup_colors(self):
        """Configuración de tema dinámico"""
        colors = {
            "dark": {
                "primary": "#2E3440",
                "secondary": "#3B4252",
                "text": "#ECEFF4",
                "accent": "#88C0D0",
            },
            "light": {
                "primary": "#ECEFF4",
                "secondary": "#E5E9F0",
                "text": "#2E3440",
                "accent": "#5E81AC",
            },
        }

        for theme, palette in colors.items():
            self.style.theme_create(
                f"{theme}_professional",
                settings={
                    "TFrame": {"configure": {"background": palette["primary"]}},
                    "TLabel": {
                        "configure": {
                            "background": palette["primary"],
                            "foreground": palette["text"],
                        }
                    },
                    "TButton": {
                        "configure": {
                            "background": palette["secondary"],
                            "foreground": palette["text"],
                            "padding": (10, 5),
                        },
                        "map": {
                            "background": [
                                ("active", palette["accent"]),
                                ("disabled", palette["secondary"]),
                            ]
                        },
                    },
                },
            )

    def setup_tooltips(self):
        """Tooltips profesionales con HTML"""
        self.tooltips = {
            "organize_button": ToolTip(
                self.organize_button,
                text="<b>Organizar Archivos</b><br>Clasifica los archivos según las reglas definidas",
                bg="white",
                fg="black",
                font=("Arial", 9),
            ),
            "undo_button": ToolTip(
                self.undo_button,
                text="<b>Deshacer</b><br>Revierte la última operación realizada",
                bg="white",
                fg="black",
                font=("Arial", 9),
            ),
        }

    def init_threads(self):
        """Inicialización avanzada de hilos con monitoreo"""
        self.thread_manager = ThreadManager()
        self.thread_manager.add_thread(
            name="TaskProcessor", target=self.process_queue, daemon=True
        )
        self.thread_manager.add_thread(
            name="Scheduler", target=self.run_scheduled_tasks, daemon=True
        )
        self.thread_manager.start_all()

    def process_queue(self):
        while self.running:
            try:
                task = self.task_queue.get(timeout=1)
                task()
            except Empty:
                continue

    def run_scheduled_tasks(self):
        while self.running:
            schedule.run_pending()
            time.sleep(1)

    def enable_scheduling(self):
        interval = self.schedule_combo.get()
        schedule.clear()
        if interval == "5 minutos":
            schedule.every(5).minutes.do(self.start_organization)
        elif interval == "1 hora":
            schedule.every().hour.do(self.start_organization)
        elif interval == "Diario":
            schedule.every().day.do(self.start_organization)

    def preview_changes(self):
        self.preview_tree.delete(*self.preview_tree.get_children())
        directory = self.dir_entry.get()
        if not os.path.exists(directory):
            return

        for filename in os.listdir(directory):
            src_path = os.path.join(directory, filename)
            if os.path.isfile(src_path):
                ext = os.path.splitext(filename)[1].lower()
                folder = self.profiles[self.current_profile]["formatos"].get(
                    ext, "Otros"
                )
                dest_path = os.path.join(directory, folder, filename)
                self.preview_tree.insert("", "end", values=(src_path, dest_path))

    def start_organization(self):
        directory = self.dir_entry.get()
        if not directory:
            messagebox.showerror("Error", "Seleccione un directorio primero")
            return

        thread = threading.Thread(
            target=self.organize_files, args=(directory,), daemon=True
        )
        thread.start()

    def organize_files(self, directory):
        """Versión segura mejorada"""
        try:
            self.validate_directory(directory)
            self.logger.info(f"Iniciando organización en: {directory}")

            files = self.safe_listdir(directory)
            total_files = len(files)
            processed = 0
            moved_files = []

            with ThreadPoolExecutor(max_workers=4) as executor:
                futures = []
                for filename in files:
                    futures.append(
                        executor.submit(self.process_single_file, directory, filename)
                    )

                for future in as_completed(futures):
                    result = future.result()
                    if result:
                        moved_files.append(result)
                        processed += 1
                        self.update_progress(processed / total_files * 100)

            self.finalize_operation(moved_files)

        except Exception as e:
            self.logger.error(f"Error en organize_files: {e}", exc_info=True)
            self.task_queue.put(
                lambda: messagebox.showerror(
                    "Error", f"No se pudo completar la operación: {str(e)}"
                )
            )

    def process_single_file(self, directory, filename):
        """Procesamiento seguro de archivos individuales"""
        try:
            src_path = os.path.join(directory, filename)
            if not self.validate_file(src_path):
                return None

            ext = os.path.splitext(filename)[1].lower()
            folder = self.profiles[self.current_profile]["formatos"].get(ext, "Otros")
            dest_dir = os.path.join(directory, folder)

            if not os.path.exists(dest_dir):
                self.safe_makedirs(dest_dir)

            dest_path = os.path.join(dest_dir, filename)
            self.safe_move(src_path, dest_path)

            self.logger.debug(f"Movido: {filename} -> {folder}")
            return (src_path, dest_path)

        except Exception as e:
            self.logger.warning(f"Error procesando {filename}: {e}")
            return None

    def safe_move(self, src, dst):
        """Movimiento seguro con verificación de hash"""
        src_hash = self.file_hash(src)
        shutil.move(src, dst)
        if self.file_hash(dst) != src_hash:
            raise IntegrityError(f"Hash mismatch after moving {src}")

    def show_stats(self, moved_files):
        stats = {
            "total": len(moved_files),
            "extensions": {},
            "size": sum(os.path.getsize(dest) for _, dest in moved_files),
        }

        for _, dest in moved_files:
            ext = os.path.splitext(dest)[1].lower()
            stats["extensions"][ext] = stats["extensions"].get(ext, 0) + 1

        message = f"Archivos movidos: {stats['total']}\n"
        message += f"Espacio liberado: {stats['size'] / 1024:.2f} KB\n"
        message += "Distribución por tipo:\n"
        for ext, count in stats["extensions"].items():
            message += f"- {ext}: {count}\n"

        self.task_queue.put(lambda: messagebox.showinfo("Estadísticas", message))

    def undo_last(self):
        if self.undo_stack:
            last_move = self.undo_stack.pop()
            for src, dest in reversed(last_move):
                try:
                    shutil.move(dest, src)
                    self.log(
                        f"Deshecho: {os.path.basename(dest)} -> {os.path.dirname(src)}"
                    )
                except Exception as e:
                    self.log(f"Error al deshacer: {str(e)}")

    def update_progress(self, value):
        self.progress["value"] = value
        self.update_idletasks()

    def setup_logging(self):
        """Configura logging avanzado con rotación de archivos"""
        self.logger = logging.getLogger("FileOrganizer")
        self.logger.setLevel(logging.DEBUG)

        # Formateador profesional
        formatter = ColoredFormatter(
            "%(asctime)s - %(name)s - %(levelname)s - %(message)s",
            datefmt="%Y-%m-%d %H:%M:%S",
        )

        # Handler para consola (colorizado)
        console = logging.StreamHandler()
        console.setFormatter(formatter)

        # Handler para archivo con rotación (10MB x 5 archivos)
        file_handler = RotatingFileHandler(
            "organizer.log", maxBytes=10 * 1024 * 1024, backupCount=5, encoding="utf-8"
        )
        file_handler.setFormatter(formatter)

        # Filtro para logs importantes
        class ImportantFilter(logging.Filter):
            def filter(self, record):
                return record.levelno >= logging.INFO

        # Configuración final
        self.logger.addHandler(console)
        self.logger.addHandler(file_handler)
        file_handler.addFilter(ImportantFilter())

        # Captura de excepciones no manejadas
        sys.excepthook = self.handle_uncaught_exception

    def handle_uncaught_exception(self, exc_type, exc_value, exc_traceback):
        """Maneja excepciones no capturadas"""
        self.logger.critical(
            "Uncaught exception", exc_info=(exc_type, exc_value, exc_traceback)
        )
        messagebox.showerror(
            "Error Crítico",
            f"Ocurrió un error no manejado: {str(exc_value)}\nVer logs para detalles.",
        )

    def save_profile(self):
        profile_name = self.profile_combo.get()
        if not profile_name:
            messagebox.showerror("Error", "Ingrese un nombre para el perfil")
            return

        self.profiles[profile_name] = {
            "directory": self.dir_entry.get(),
            "formatos": self.get_current_formats(),
            "schedule": self.schedule_combo.get(),
        }

        self.save_to_file()
        self.load_profiles()
        messagebox.showinfo("Éxito", f"Perfil '{profile_name}' guardado")

    def load_profiles(self):
        try:
            with open("profiles.json", "r") as f:
                self.profiles = json.load(f)
        except FileNotFoundError:
            self.profiles = {
                "default": {
                    "directory": "",
                    "formatos": self.default_formats,
                    "schedule": "Ninguna",
                }
            }

        self.profile_combo["values"] = list(self.profiles.keys())
        self.profile_combo.set("default")
        self.load_profile_settings()

    def load_profile_settings(self):
        profile = self.profiles[self.current_profile]
        self.dir_entry.delete(0, END)
        self.dir_entry.insert(0, profile["directory"])
        self.schedule_combo.set(profile["schedule"])
        self.update_format_tree(profile["formatos"])

    def update_format_tree(self, formatos):
        self.format_tree.delete(*self.format_tree.get_children())
        for ext, folder in formatos.items():
            self.format_tree.insert("", END, values=(ext, folder))

    def get_current_formats(self):
        formatos = {}
        for child in self.format_tree.get_children():
            ext, folder = self.format_tree.item(child)["values"]
            formatos[ext] = folder
        return formatos

    def delete_profile(self):
        profile_name = self.profile_combo.get()
        if profile_name == "default":
            messagebox.showerror(
                "Error", "No se puede eliminar el perfil predeterminado"
            )
            return

        del self.profiles[profile_name]
        self.save_to_file()
        self.load_profiles()
        messagebox.showinfo("Éxito", f"Perfil '{profile_name}' eliminado")

    def save_to_file(self):
        with open("profiles.json", "w") as f:
            json.dump(self.profiles, f)

    def add_format(self):
        def save_new_format():
            ext = ext_entry.get().strip()
            folder = folder_entry.get().strip()
            if ext and folder:
                self.format_tree.insert("", END, values=(ext, folder))
                top.destroy()

        top = Toplevel(self)
        top.title("Agregar Formato")

        ttk.Label(top, text="Extensión (ej. .jpg):").pack(padx=10, pady=2)
        ext_entry = ttk.Entry(top)
        ext_entry.pack(padx=10, pady=2)

        ttk.Label(top, text="Carpeta destino:").pack(padx=10, pady=2)
        folder_entry = ttk.Entry(top)
        folder_entry.pack(padx=10, pady=2)

        ttk.Button(top, text="Guardar", command=save_new_format).pack(pady=10)

    def remove_format(self):
        selected = self.format_tree.selection()
        if selected:
            self.format_tree.delete(selected[0])

    def on_closing(self):
        """Cierre profesional con limpieza"""
        self.logger.info("Iniciando cierre de aplicación")
        try:
            if hasattr(self, "thread_manager"):
                self.thread_manager.stop_all()

            # Guardar estado
            self.save_to_file()
            self.logger.info("Aplicación cerrada correctamente")
        except Exception as e:
            self.logger.error(f"Error durante el cierre: {e}")
        finally:
            self.destroy()

    def setup_performance_optimizations(self):
        """Configuración avanzada y correcta de optimizaciones"""
        try:
            # 1. Configuración de estilos para Treeview (forma correcta)
            self.style = ttk.Style()

            # Estilo base para todos los Treeviews
            self.style.configure(
                "Treeview",
                rowheight=25,
                font=("Segoe UI", 9),
                background="#ffffff",
                fieldbackground="#ffffff",
            )

            # Estilo para los encabezados
            self.style.configure(
                "Treeview.Heading",
                font=("Segoe UI", 9, "bold"),
                padding=(5, 2, 5, 2),
                background="#f0f0f0",
            )

            # Estilo para items seleccionados
            self.style.map(
                "Treeview",
                background=[("selected", "#0078d7")],
                foreground=[("selected", "white")],
            )

            # 2. Configuración específica de los widgets (forma correcta)
            if hasattr(self, "format_tree"):
                self.format_tree.configure(style="Treeview")  # Usar el estilo definido

                # Configuración de columnas (alternativa correcta a displaycolumns)
                cols = self.format_tree["columns"]
                if cols:
                    self.format_tree.configure(columns=cols, show="headings")

            if hasattr(self, "preview_tree"):
                self.preview_tree.configure(style="Treeview")

            # 3. Sistema de caché mejorado
            self.setup_caching_system()

            # 4. Precarga en segundo plano
            self.start_background_cache_builder()

            self.logger.info("Optimizaciones de rendimiento configuradas correctamente")

        except Exception as e:
            self.logger.error(f"Error configurando optimizaciones: {e}", exc_info=True)
            messagebox.showwarning(
                "Advertencia",
                "Algunas optimizaciones no se aplicaron completamente.\n"
                "La aplicación funcionará pero con rendimiento reducido.",
            )

    def setup_caching_system(self):
        """Configura el sistema de caché avanzado"""

        # Caché para operaciones de archivos
        self.file_cache = TTLCache(
            maxsize=1000,  # ~1MB de memoria
            ttl=300,  # 5 minutos de vida
        )

        # Caché para estructura de directorios
        self.dir_cache = TTLCache(
            maxsize=500,  # ~500KB
            ttl=180,  # 3 minutos
        )

        # Caché para imágenes y recursos
        self.resource_cache = {}

    def start_background_cache_builder(self):
        """Inicia el precaché en segundo plano"""

        def cache_builder():
            while getattr(self, "running", True):
                try:
                    self.warmup_caches()
                    time.sleep(30)  # Actualizar caché cada 30 segundos
                except Exception as e:
                    self.logger.warning(f"Error en cache_builder: {e}")
                    time.sleep(5)

        if not hasattr(self, "cache_thread") or not self.cache_thread.is_alive():
            self.cache_thread = threading.Thread(
                target=cache_builder, name="CacheBuilder", daemon=True
            )
            self.cache_thread.start()

    def warmup_caches(self):
        """Precarga datos en los cachés"""
        # Precargar perfiles y formatos
        for profile in self.profiles.values():
            cache_key = f"profile_{profile['name']}"
            self.file_cache[cache_key] = profile

        # Precargar estructura de directorios recientes
        recent_dirs = [p["directory"] for p in self.profiles.values()]
        for directory in recent_dirs:
            if os.path.isdir(directory):
                self.dir_cache[directory] = os.listdir(directory)


if __name__ == "__main__":
    app = FileOrganizerGUI()
    app.protocol("WM_DELETE_WINDOW", app.on_closing)
    app.mainloop()
