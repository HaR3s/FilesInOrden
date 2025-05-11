import os
import sys
import time
import json
import logging
import threading
import hashlib
from datetime import datetime
from collections import deque
from queue import Queue, Empty
from typing import Dict, Optional, List, Tuple  # Tipado adicional
from logging.handlers import RotatingFileHandler
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Callable
from concurrent.futures import Future

# Tkinter y GUI
from tkinter import *
import tkinter as tk
from tkinter import (
    Tk,
    StringVar,
    BooleanVar,
    IntVar,
    filedialog,
    messagebox,
    scrolledtext,
)
from tkinter import ttk
from PIL import Image, ImageTk  # Requiere pillow

# Utilidades del sistema
import psutil
import shutil
import schedule

# Librerías de terceros
from cachetools import TTLCache
from coloredlogs import ColoredFormatter


# TODO: Crear la clase para tratar errores
class IntegrityError(Exception):
    """Excepción para errores de integridad de archivos"""

    pass


class ThreadManager:
    def __init__(self):
        self.threads = {}
        self.lock = threading.Lock()
        self.stop_event = threading.Event()  # Nuevo

    def _thread_wrapper(self, name, target):
        """Hilo que verifica stop_event periódicamente"""
        while not self.stop_event.is_set():  # <-- Bucle controlado
            try:
                self.threads[name]["active"] = True
                target()  # Debe ser una función en bucle
            except Exception as e:
                logging.error(f"Thread {name} error: {str(e)}", exc_info=True)
            finally:
                self.threads[name]["active"] = False

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

    def start_all(self):
        for thread_info in self.threads.values():
            thread_info["thread"].start()

    def stop_all(self, timeout=5):
        self.stop_event.set()  # Señal de parada para todos los hilos
        for name, thread_info in self.threads.items():
            if thread_info["thread"].is_alive():
                thread_info["thread"].join(timeout)


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
        self.task_queue = Queue(maxsize=100)
        self.setup_logging()  # Primero el logging
        self.logger.info("Inicializando aplicación")
        self.performance_cache = {
            "directory_scan": TTLCache(maxsize=100, ttl=30),
            "file_operations": TTLCache(maxsize=500, ttl=60),
        }
        self.running = True
        self.theme_mode = "light"
        self.load_profiles()
        self.create_widgets()
        self.setup_performance_optimizations()
        self.update_theme()
        self.init_threads()
        self.load_icons_async()
        self.title("Organizador Avanzado de Archivos")
        self.geometry("900x700")
        self.configure(bg="#f0f0f0")
        self.profiles = {}
        self.current_profile = "default"
        self.undo_stack = deque(maxlen=5)
        self.task_queue = Queue()

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
        self.load_profiles()

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

    def log(self, message):
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.log_area.insert(END, f"[{timestamp}] {message}\n")
        self.log_area.see(END)

    def select_directory(self):
        directory = filedialog.askdirectory(title="Seleccionar carpeta a organizar")
        if directory:  # Si el usuario no cancela
            self.dir_entry.delete(0, tk.END)
            self.dir_entry.insert(0, directory)

    def build_operations_tab(self, parent):
        """Construye la pestaña de operaciones principales"""
        # Frame principal con scroll
        main_frame = ttk.Frame(parent)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Panel de directorio
        dir_frame = ttk.LabelFrame(
            main_frame, text="Selección de Directorio", padding=10
        )
        dir_frame.pack(fill=tk.X, pady=(0, 10))

        ttk.Label(dir_frame, text="Directorio a organizar:").pack(anchor=tk.W)
        self.dir_entry = ttk.Entry(dir_frame)
        self.dir_entry.pack(fill=tk.X, pady=5)
        ttk.Button(dir_frame, text="Examinar", command=self.select_directory).pack(
            pady=5
        )

        # Panel de acciones
        action_frame = ttk.LabelFrame(main_frame, text="Acciones", padding=10)
        action_frame.pack(fill=tk.X, pady=(0, 10))

        btn_grid = ttk.Frame(action_frame)
        btn_grid.pack()

        buttons = [
            ("Previsualizar", self.preview_changes, 0, 0),
            ("Organizar Ahora", self.start_organization, 0, 1),
            ("Deshacer", self.undo_last, 1, 0),
            ("Estadísticas", self.show_stats, 1, 1),
        ]

        for text, command, row, col in buttons:
            btn = ttk.Button(
                btn_grid, text=text, command=command, style="Accent.TButton"
            )
            btn.grid(row=row, column=col, padx=5, pady=5, sticky=tk.NSEW)

        # Panel de progreso
        progress_frame = ttk.LabelFrame(main_frame, text="Progreso", padding=10)
        progress_frame.pack(fill=tk.X)

        self.progress = ttk.Progressbar(
            progress_frame, orient=tk.HORIZONTAL, mode="determinate"
        )
        self.progress.pack(fill=tk.X, pady=5)

        # Configuración de estilo para botón destacado
        self.style.configure("Accent.TButton", foreground="white", background="#0078d7")

    def build_config_tab(self, parent):
        """Construye la pestaña de configuración avanzada"""
        notebook = ttk.Notebook(parent)
        notebook.pack(fill=tk.BOTH, expand=True)

        # Subpestaña de Perfiles
        profile_tab = ttk.Frame(notebook, padding=10)
        self.build_profile_settings(profile_tab)
        notebook.add(profile_tab, text="Perfiles")

        # Subpestaña de Formatos
        format_tab = ttk.Frame(notebook, padding=10)
        self.build_format_settings(format_tab)
        notebook.add(format_tab, text="Formatos")

        # Subpestaña de Apariencia
        appearance_tab = ttk.Frame(notebook, padding=10)
        self.build_appearance_settings(appearance_tab)
        notebook.add(appearance_tab, text="Apariencia")

    def build_profile_settings(self, parent):
        """Construye el panel de configuración de perfiles"""
        frame = ttk.LabelFrame(parent, text="Gestión de Perfiles", padding=10)
        frame.pack(fill=tk.X, pady=5)

        ttk.Label(frame, text="Perfil actual:").pack(anchor=tk.W)
        self.profile_combo = ttk.Combobox(frame)
        self.profile_combo.pack(fill=tk.X, pady=5)

        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill=tk.X)

        profile_buttons = [
            ("Guardar", self.save_profile),
            ("Eliminar", self.delete_profile),
            ("Nuevo", self.create_new_profile),
        ]

        for text, command in profile_buttons:
            btn = ttk.Button(btn_frame, text=text, command=command)
            btn.pack(side=tk.LEFT, padx=5, pady=5, expand=True)

    def import_formats(self):
        """Importa formatos desde un archivo JSON"""
        filepath = filedialog.askopenfilename(
            title="Importar formatos",
            filetypes=[("Archivos JSON", "*.json"), ("Todos los archivos", "*.*")],
            defaultextension=".json",
        )

        if not filepath:  # Usuario canceló
            return

        try:
            with open(filepath, "r", encoding="utf-8") as f:
                formats = json.load(f)

                # Validar estructura del archivo
                if not isinstance(formats, dict):
                    raise ValueError(
                        "El archivo debe contener un diccionario de formatos"
                    )

                # Actualizar el perfil actual
                self.profiles[self.current_profile]["formatos"] = formats
                self.update_format_tree(formats)

                self.logger.info(f"Formatos importados desde {filepath}")
                messagebox.showinfo("Éxito", "Formatos importados correctamente")

        except json.JSONDecodeError:
            messagebox.showerror("Error", "El archivo no es un JSON válido")
            self.logger.error("Error al decodificar JSON de formatos")
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo importar: {str(e)}")
            self.logger.error(f"Error importando formatos: {e}", exc_info=True)

    def export_formats(self):
        """Exporta los formatos actuales a un archivo JSON"""
        filepath = filedialog.asksaveasfilename(
            title="Exportar formatos",
            filetypes=[("Archivos JSON", "*.json"), ("Todos los archivos", "*.*")],
            defaultextension=".json",
            initialfile=f"formatos_{self.current_profile}.json",
        )

        if not filepath:  # Usuario canceló
            return

        try:
            formats = self.get_current_formats()

            with open(filepath, "w", encoding="utf-8") as f:
                json.dump(formats, f, indent=4, ensure_ascii=False)

            self.logger.info(f"Formatos exportados a {filepath}")
            messagebox.showinfo("Éxito", "Formatos exportados correctamente")

        except Exception as e:
            messagebox.showerror("Error", f"No se pudo exportar: {str(e)}")
            self.logger.error(f"Error exportando formatos: {e}", exc_info=True)

    def build_format_settings(self, parent):
        """Construye el panel de configuración de formatos"""
        main_frame = ttk.Frame(parent)
        main_frame.pack(fill=tk.BOTH, expand=True)

        # Barra de búsqueda
        search_frame = ttk.Frame(main_frame)
        search_frame.pack(fill=tk.X, pady=5)

        ttk.Label(search_frame, text="Buscar:").pack(side=tk.LEFT)
        self.search_entry = ttk.Entry(search_frame)
        self.search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        self.search_entry.bind("<KeyRelease>", self.filter_formats)

        # Treeview de formatos
        tree_frame = ttk.Frame(main_frame)
        tree_frame.pack(fill=tk.BOTH, expand=True)

        self.format_tree = ttk.Treeview(
            tree_frame, columns=("ext", "folder"), show="headings", selectmode="browse"
        )
        self.format_tree.heading("ext", text="Extensión")
        self.format_tree.heading("folder", text="Carpeta Destino")
        self.format_tree.column("ext", width=100)
        self.format_tree.column("folder", width=200)

        vsb = ttk.Scrollbar(
            tree_frame, orient="vertical", command=self.format_tree.yview
        )
        hsb = ttk.Scrollbar(
            tree_frame, orient="horizontal", command=self.format_tree.xview
        )
        self.format_tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        self.format_tree.grid(row=0, column=0, sticky=tk.NSEW)
        vsb.grid(row=0, column=1, sticky=tk.NS)
        hsb.grid(row=1, column=0, sticky=tk.EW)

        tree_frame.grid_columnconfigure(0, weight=1)
        tree_frame.grid_rowconfigure(0, weight=1)

        # Controles de formatos
        ctrl_frame = ttk.Frame(main_frame)
        ctrl_frame.pack(fill=tk.X, pady=5)

        ttk.Button(ctrl_frame, text="Agregar", command=self.add_format).pack(
            side=tk.LEFT, padx=5
        )
        ttk.Button(ctrl_frame, text="Eliminar", command=self.remove_format).pack(
            side=tk.LEFT, padx=5
        )
        ttk.Button(ctrl_frame, text="Importar", command=self.import_formats).pack(
            side=tk.RIGHT, padx=5
        )
        ttk.Button(ctrl_frame, text="Exportar", command=self.export_formats).pack(
            side=tk.RIGHT, padx=5
        )

    def change_theme(self, event=None):
        """Cambia el tema visual de toda la aplicación"""
        try:
            # Mapeo de nombres de temas a configuraciones
            theme_mapping = {
                "Claro": {
                    "style": "light",
                    "bg": "#f0f0f0",
                    "fg": "#000000",
                    "accent": "#0078d7",
                },
                "Oscuro": {
                    "style": "dark",
                    "bg": "#2d2d2d",
                    "fg": "#ffffff",
                    "accent": "#0e639c",
                },
                "Profesional": {
                    "style": "professional",
                    "bg": "#f5f5f5",
                    "fg": "#212121",
                    "accent": "#607d8b",
                },
                "Sistema": {
                    "style": "clam",
                    "bg": "default",
                    "fg": "default",
                    "accent": "default",
                },
            }

            selected_theme = self.theme_combo.get()
            theme_config = theme_mapping.get(selected_theme, theme_mapping["Sistema"])

            # 1. Aplicar estilo ttk
            self.style.theme_use(theme_config["style"])

            # 2. Configurar colores base
            self.style.configure(
                ".",
                background=theme_config["bg"],
                foreground=theme_config["fg"],
                fieldbackground=theme_config["bg"],
            )

            # 3. Configurar widgets específicos
            self.style.configure("TFrame", background=theme_config["bg"])
            self.style.configure(
                "TLabel", background=theme_config["bg"], foreground=theme_config["fg"]
            )
            self.style.configure(
                "TButton",
                background=theme_config["accent"],
                foreground="white",
                font=("Segoe UI", 9),
            )
            self.style.map(
                "TButton",
                background=[
                    ("active", theme_config["accent"]),
                    ("disabled", "#cccccc"),
                ],
            )

            # 4. Actualizar widgets no-ttk
            self.update_non_ttk_widgets(theme_config)

            # 5. Guardar preferencia
            self.theme_mode = theme_config["style"]
            self.logger.info(f"Tema cambiado a: {selected_theme}")

        except Exception as e:
            self.logger.error(f"Error cambiando tema: {e}", exc_info=True)
            messagebox.showerror("Error", f"No se pudo cambiar el tema: {str(e)}")

    def update_non_ttk_widgets(self, theme_config):
        """Actualiza widgets que no son ttk y ajusta los Treeviews"""
        try:
            # 1. Área de texto del log (widget estándar)
            self.log_area.configure(
                bg=theme_config["bg"],
                fg=theme_config["fg"],
                insertbackground=theme_config["fg"],
            )

            # 2. Configurar Treeviews mediante estilos (forma correcta)
            self.style.configure(
                "Treeview",
                background=theme_config["bg"],
                foreground=theme_config["fg"],
                fieldbackground=theme_config["bg"],
                rowheight=25,  # Mantener configuración previa
            )

            # Estilo para items seleccionados
            self.style.map(
                "Treeview",
                background=[("selected", theme_config["accent"])],
                foreground=[("selected", "white")],
            )

            # 3. Ventana principal
            self.configure(background=theme_config["bg"])

            # 4. Forzar actualización de los Treeviews
            self.format_tree.update_idletasks()
            if hasattr(self, "preview_tree"):
                self.preview_tree.update_idletasks()

        except Exception as e:
            self.logger.error(f"Error actualizando widgets: {e}", exc_info=True)

    def build_appearance_settings(self, parent):
        """Construye el panel de configuración de apariencia"""
        frame = ttk.LabelFrame(parent, text="Personalización", padding=10)
        frame.pack(fill=tk.BOTH, expand=True, pady=5)

        # Selector de tema
        ttk.Label(frame, text="Tema visual:").pack(anchor=tk.W)
        self.theme_combo = ttk.Combobox(
            frame, values=["Claro", "Oscuro", "Profesional", "Sistema"]
        )
        self.theme_combo.pack(fill=tk.X, pady=5)
        self.theme_combo.bind("<<ComboboxSelected>>", self.change_theme)

        # Configuración de fuente
        font_frame = ttk.LabelFrame(frame, text="Fuente", padding=10)
        font_frame.pack(fill=tk.X, pady=5)

        ttk.Label(font_frame, text="Tamaño:").grid(row=0, column=0, sticky=tk.W)
        self.font_size = ttk.Combobox(
            font_frame, values=["8", "9", "10", "11", "12"], width=5
        )
        self.font_size.grid(row=0, column=1, sticky=tk.W, padx=5)
        self.font_size.set("9")

        # Configuración de iconos
        ttk.Checkbutton(
            frame,
            text="Mostrar iconos en los archivos",
            variable=tk.BooleanVar(value=True),
        ).pack(anchor=tk.W, pady=5)

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

    def save_to_file(self):
        with open("profiles.json", "w") as f:
            json.dump(self.profiles, f)

    def create_new_profile(self):
        """Placeholder para futura implementación"""
        messagebox.showinfo("Info", "Función de nuevo perfil no implementada aún")

    def save_profile(self):
        profile_name = self.profile_combo.get()
        if not profile_name:
            messagebox.showerror("Error", "Ingrese un nombre para el perfil")
            return

        self.profiles[profile_name] = {
            "directory": self.dir_entry.get(),
            "formatos": self.get_current_formats(),
            # "schedule": self.schedule_combo.get(),
        }

        self.save_to_file()
        self.load_profiles()
        messagebox.showinfo("Éxito", f"Perfil '{profile_name}' guardado")

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

    def load_profiles(self):
        """
        Carga los perfiles desde el archivo JSON con manejo robusto de errores.
        Si el archivo no existe o está corrupto, crea un perfil predeterminado.
        """
        profile_path = os.path.abspath("profiles.json")  # Usar ruta absoluta
        self.logger.info(f"Cargando perfiles desde: {profile_path}")

        try:
            with open(profile_path, "r", encoding="utf-8") as f:
                self.profiles = json.load(f)

            # Validar estructura básica
            if not isinstance(self.profiles, dict):
                raise json.JSONDecodeError("Formato inválido", doc=profile_path, pos=0)

            self.logger.info(f"Perfiles cargados: {len(self.profiles)}")

        except (FileNotFoundError, json.JSONDecodeError, AttributeError) as e:
            self.logger.warning(
                f"Error cargando perfiles ({type(e).__name__}), creando predeterminado"
            )

            self.profiles = {
                "default": {
                    "name": "default",
                    "directory": "",
                    "formatos": self.default_formats.copy(),  # Copia para evitar mutaciones
                    "created_at": datetime.now().isoformat(),  # Metadata adicional
                }
            }
            self.save_to_file()  # Guardar inmediatamente

    def load_profile_settings(self):
        profile = self.profiles[self.current_profile]
        self.dir_entry.delete(0, END)
        self.dir_entry.insert(0, profile["directory"])
        # self.schedule_combo.set(profile["schedule"])
        self.update_format_tree(profile["formatos"])

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

    # def build_configuration_panel(self, parent):
    #     # Configuración de directorio
    #     dir_frame = ttk.LabelFrame(parent, text="Directorio")
    #     dir_frame.pack(padx=10, pady=5, fill=X)
    #
    #     self.dir_entry = ttk.Entry(dir_frame)
    #     self.dir_entry.pack(side=LEFT, fill=X, expand=True, padx=5)
    #
    #     ttk.Button(dir_frame, text="Examinar", command=self.select_directory).pack(
    #         side=LEFT
    #     )
    #
    #     # Configuración de perfiles
    #     profile_frame = ttk.LabelFrame(parent, text="Perfiles")
    #     profile_frame.pack(padx=10, pady=5, fill=X)
    #
    #     self.profile_combo = ttk.Combobox(profile_frame)
    #     self.profile_combo.pack(side=LEFT, fill=X, expand=True, padx=5)
    #     ttk.Button(profile_frame, text="Guardar", command=self.save_profile).pack(
    #         side=LEFT
    #     )
    #     ttk.Button(profile_frame, text="Eliminar", command=self.delete_profile).pack(
    #         side=LEFT
    #     )
    #
    #     # Configuración de formatos
    #     format_frame = ttk.LabelFrame(parent, text="Formatos de Archivo")
    #     format_frame.pack(padx=10, pady=5, fill=BOTH, expand=True)
    #
    #     self.search_entry = ttk.Entry(format_frame)
    #     self.search_entry.pack(fill=X, padx=5, pady=2)
    #     self.search_entry.bind("<KeyRelease>", self.filter_formats)
    #
    #     self.format_tree = ttk.Treeview(
    #         format_frame, columns=("ext", "folder"), show="headings"
    #     )
    #     self.format_tree.heading("ext", text="Extensión")
    #     self.format_tree.heading("folder", text="Carpeta")
    #     self.format_tree.pack(fill=BOTH, expand=True)
    #
    #     control_frame = ttk.Frame(format_frame)
    #     control_frame.pack(pady=5)
    #     ttk.Button(control_frame, text="Agregar", command=self.add_format).pack(
    #         side=LEFT
    #     )
    #     ttk.Button(control_frame, text="Eliminar", command=self.remove_format).pack(
    #         side=LEFT
    #     )
    #
    #     # Configuración de programación
    #     schedule_frame = ttk.LabelFrame(parent, text="Programación")
    #     schedule_frame.pack(padx=10, pady=5, fill=X)
    #
    #     self.schedule_combo = ttk.Combobox(
    #         schedule_frame, values=["Ninguna", "5 minutos", "1 hora", "Diario"]
    #     )
    #     self.schedule_combo.pack(side=LEFT, padx=5)
    #     ttk.Button(schedule_frame, text="Activar", command=self.enable_scheduling).pack(
    #         side=LEFT
    #     )
    #
    #     # Barra de progreso
    #     self.progress = ttk.Progressbar(parent, orient=HORIZONTAL, mode="determinate")
    #     self.progress.pack(padx=10, pady=5, fill=X)
    #
    #     # Controles principales
    #     control_frame = ttk.Frame(parent)
    #     control_frame.pack(pady=10)
    #     ttk.Button(
    #         control_frame, text="Previsualizar", command=self.preview_changes
    #     ).pack(side=LEFT, padx=5)
    #     ttk.Button(
    #         control_frame, text="Organizar Ahora", command=self.start_organization
    #     ).pack(side=LEFT, padx=5)
    #     ttk.Button(control_frame, text="Deshacer", command=self.undo_last).pack(
    #         side=LEFT, padx=5
    #     )
    #     ttk.Button(control_frame, text="Tema", command=self.toggle_theme).pack(
    #         side=LEFT, padx=5
    #     )

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
        """
        Carga los íconos en segundo plano con manejo de errores y valores por defecto.
        """
        self.icon_cache = {
            "default": self.create_default_icon("gray"),
            "error": self.create_default_icon("red"),  # Ícono para errores
        }

        def _load_icons():
            icon_mapping = {
                "file": ("document.png", "blue"),
                "folder": ("folder.png", "green"),
                "image": ("image.png", "yellow"),
                # ... otros íconos
            }

            for icon_name, (filename, fallback_color) in icon_mapping.items():
                try:
                    icon_path = os.path.join("icons", filename)
                    if os.path.exists(icon_path):
                        self.icon_cache[icon_name] = tk.PhotoImage(file=icon_path)
                    else:
                        self.logger.warning(f"Ícono no encontrado: {icon_path}")
                        self.icon_cache[icon_name] = self.create_default_icon(
                            fallback_color
                        )
                except Exception as e:
                    self.logger.error(f"Error cargando ícono {icon_name}: {str(e)}")
                    self.icon_cache[icon_name] = self.icon_cache["error"]

        # Ejecutar en hilo con nombre para debugging
        threading.Thread(target=_load_icons, name="IconLoader", daemon=True).start()

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

    def load_icons(self) -> None:
        """Carga todos los iconos necesarios con manejo seguro de tipos"""
        self.icons: Dict[
            str, tk.PhotoImage
        ] = {}  # Especificamos el tipo explícitamente

        # Lista de iconos requeridos
        required_icons = {
            "file": self.create_default_icon("gray"),
            "folder": self.create_default_icon("blue"),
            "document": self.load_icon_safely("document.png"),
            "image": self.load_icon_safely("image.png"),
            "video": self.load_icon_safely("video.png"),
            "audio": self.load_icon_safely("audio.png"),
            "archive": self.load_icon_safely("archive.png"),
        }

        self.icons.update({k: v for k, v in required_icons.items() if v is not None})

        # Asegurarse de que al menos tenemos el icono 'file'
        if "file" not in self.icons:
            self.icons["file"] = self.create_default_icon("gray")

    def load_icon_safely(self, filename: str) -> Optional[tk.PhotoImage]:
        """Carga un icono con manejo de errores"""
        try:
            return tk.PhotoImage(file=f"icons/{filename}")
        except Exception as e:
            self.logger.warning(f"No se pudo cargar icono {filename}: {e}")
            return None

    def create_default_icon(
        self, color: str, size: tuple[int, int] = (16, 16)
    ) -> tk.PhotoImage:
        """
        Crea un ícono por defecto compatible con el sistema de tipos de PyCharm/IDEs.

        Args:
            color (str): Nombre del color (ej: 'gray') o código HEX (ej: '#FF0000')
            size (tuple[int, int]): Tamaño del ícono en píxeles (ancho, alto). Default: (16, 16)

        Returns:
            tk.PhotoImage: Objeto de imagen compatible con tkinter

        Raises:
            ValueError: Si el tamaño no es una tupla de 2 enteros positivos
        """
        # Validación de parámetros
        if (
            not isinstance(size, tuple)
            or len(size) != 2
            or not all(isinstance(dim, int) and dim > 0 for dim in size)
        ):
            raise ValueError("El tamaño debe ser una tupla de 2 enteros positivos")

        # Try Pillow (mejor calidad)
        try:
            from PIL import Image, ImageTk

            img = Image.new("RGB", size, color)
            pil_icon = ImageTk.PhotoImage(img)

            # Conversión segura al tipo tk.PhotoImage para el type checker
            tk_icon = tk.PhotoImage(width=size[0], height=size[1])
            tk_icon.__dict__ = pil_icon.__dict__  # Copia todas las propiedades
            return tk_icon

        except ImportError:  # Fallback a tkinter puro
            self.logger.debug("Pillow no disponible, creando ícono básico")
            try:
                # Intentar crear ícono con transparencia (si el color es None)
                if color.lower() == "transparent":
                    icon = tk.PhotoImage(width=size[0], height=size[1])
                    icon.transparency_set(0, 0, True)  # Hacer transparente)
            except tk.TclError:
                # Último fallback para versiones antiguas de tkinter
                return tk.PhotoImage(width=size[0], height=size[1])

    def get_icon_for_extension(self, extension: str) -> tk.PhotoImage:
        """Versión completamente tipada que nunca devuelve None"""
        icon_type = self._get_icon_type(extension)
        return self.icons.get(icon_type, self.icons["file"])

    def _get_icon_type(self, extension: str) -> str:
        """Determina el tipo de icono para una extensión"""
        extension = extension.lower()
        icon_mapping = {
            "document": [".pdf", ".doc", ".docx", ".txt", ".rtf"],
            "image": [".jpg", ".jpeg", ".png", ".gif", ".bmp"],
            "video": [".mp4", ".avi", ".mov", ".mkv"],
            "audio": [".mp3", ".wav", ".flac", ".aac"],
            "archive": [".zip", ".rar", ".7z", ".tar"],
        }

        for icon_type, extensions in icon_mapping.items():
            if extension in extensions:
                return icon_type
        return "file"

    def setup_animations(self):
        pass

    def setup_statusbar(self):
        pass

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
                self.organize_files,
                text="<b>Organizar Archivos</b><br>Clasifica los archivos según las reglas definidas",
                bg="white",
                fg="black",
                font=("Arial", 9),
            ),
            "undo_button": ToolTip(
                self.undo_last,
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

    # def enable_scheduling(self):
    #     interval = self.schedule_combo.get()
    #     schedule.clear()
    #     if interval == "5 minutos":
    #         schedule.every(5).minutes.do(self.start_organization)
    #     elif interval == "1 hora":
    #         schedule.every().hour.do(self.start_organization)
    #     elif interval == "Diario":
    #         schedule.every().day.do(self.start_organization)

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

    def validate_directory(self, directory):
        if not os.path.isdir(directory):
            raise ValueError(f"Directorio no válido: {directory}")
        if not os.access(directory, os.R_OK | os.W_OK):
            raise PermissionError(f"Sin permisos en: {directory}")
        return True

    def safe_listdir(self, directory: str) -> List[str]:
        """Lista los contenidos de un directorio de forma segura.

        Args:
            directory: Ruta del directorio

        Returns:
            List[str]: Lista de nombres de archivos/directorios

        Raises:
            OSError: Si falla la lectura del directorio
        """
        try:
            return [
                f for f in os.listdir(directory) if not f.startswith(".")
            ]  # Ignorar archivos ocultos
        except Exception as e:
            self.logger.error(f"Error leyendo directorio {directory}: {e}")
            raise OSError(f"No se pudo leer el directorio: {directory}") from e

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

    def process_results(self, futures: List[Future]) -> None:
        """Procesa los resultados de las operaciones concurrentes.

        Args:
            futures: Lista de Futures del ThreadPoolExecutor

        Updates:
            - Barra de progreso
            - Registro de operaciones
            - Estadísticas
        """
        moved_files = []
        total = len(futures)

        for i, future in enumerate(as_completed(futures), 1):
            try:
                result = future.result()
                if result:
                    moved_files.append(result)

                    # Actualizar UI en el hilo principal
                    self.update_ui_from_thread(
                        lambda: self.update_progress(i / total * 100)
                    )

            except Exception as e:
                self.logger.warning(f"Error procesando archivo: {e}")

        # Mostrar estadísticas finales
        self.update_ui_from_thread(lambda: self.show_stats(moved_files))

        # Guardar para posible undo
        if moved_files:
            self.undo_stack.append(moved_files)

    def validate_file(self, src_path: str) -> bool:
        """Valida un archivo antes de procesarlo.

        Realiza múltiples comprobaciones para asegurar que el archivo:
        - Existe y es accesible
        - No está en uso por otro proceso
        - Tiene permisos adecuados
        - No es un archivo del sistema/protegido
        - Cumple con requisitos básicos de seguridad

        Args:
            src_path: Ruta completa al archivo a validar

        Returns:
            bool: True si el archivo es válido para procesar, False en caso contrario

        Raises:
            OSError: Para problemas de permisos o acceso
            IntegrityError: Para problemas de integridad del archivo
        """
        try:
            # 1. Verificar que la ruta existe y es un archivo (no directorio)
            if not os.path.isfile(src_path):
                self.logger.warning(f"La ruta no es un archivo: {src_path}")
                return False

            # 2. Verificar permisos de lectura
            if not os.access(src_path, os.R_OK):
                self.logger.error(f"Sin permisos de lectura: {src_path}")
                raise PermissionError(f"No se puede leer el archivo: {src_path}")

            # 3. Verificar que el archivo no esté en uso (Multiplataforma)
            if os.name == "nt":  # Windows
                # Intento de apertura exclusiva
                with open(src_path, "rb+") as f:
                    pass
            else:  # Linux/macOS
                # Usar lsof para verificar si el archivo está abierto
                import subprocess

                result = subprocess.run(
                    ["lsof", src_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE
                )
                if result.returncode == 0:
                    self.logger.warning(f"Archivo en uso (Linux): {src_path}")
                    return False

            # 4. Verificar que no sea un archivo del sistema/protegido
            filename = os.path.basename(src_path)
            if filename.startswith(("~$", "Thumbs.db", ".DS_Store", "desktop.ini")):
                self.logger.debug(f"Ignorando archivo del sistema: {filename}")
                return False

            # 5. Verificar tamaño mínimo/máximo (opcional)
            file_size = os.path.getsize(src_path)
            if file_size == 0:
                self.logger.warning(f"Archivo vacío: {src_path}")
                return False
            if file_size > 100 * 1024 * 1024:  # 100MB
                self.logger.warning(f"Archivo demasiado grande (>100MB): {src_path}")
                return False

            # 6. Verificar extensión válida (opcional)
            ext = os.path.splitext(filename)[1].lower()
            if ext not in self.profiles[self.current_profile]["formatos"]:
                self.logger.debug(f"Extensión no configurada: {ext} en {filename}")
                # No retornamos False aquí porque queremos permitir la categoría "Otros"

            # 7. Verificar integridad básica (para ciertos tipos de archivos)
            if ext in (".jpg", ".png", ".pdf", ".docx"):
                if not self._validate_file_signature(src_path, ext):
                    self.logger.error(f"Firma de archivo inválida: {src_path}")
                    raise IntegrityError(f"Archivo corrupto o inválido: {src_path}")

            return True

        except (IOError, PermissionError, FileNotFoundError):
            return False
        except Exception as e:
            self.logger.error(f"Error verificando uso del archivo: {e}")
            return False

    def _validate_file_signature(self, filepath: str, ext: str) -> bool:
        """Valida la firma (magic numbers) de un archivo.

        Args:
            filepath: Ruta al archivo
            ext: Extensión del archivo

        Returns:
            bool: True si la firma coincide con la extensión
        """
        # Mapeo de firmas conocidas (primeros bytes)
        SIGNATURES = {
            ".jpg": [b"\xff\xd8\xff"],
            ".png": [b"\x89PNG\r\n\x1a\n"],
            ".pdf": [b"%PDF"],
            ".docx": [b"PK\x03\x04"],  # DOCX es un ZIP
        }

        if ext not in SIGNATURES:
            return True  # No validamos extensiones desconocidas

        try:
            with open(filepath, "rb") as f:
                header = f.read(8)  # Leer suficientes bytes para las firmas

            return any(header.startswith(sig) for sig in SIGNATURES[ext])
        except Exception:
            return False

    def safe_makedirs(self, directory: str) -> None:
        """Crea directorios de forma segura con manejo de errores.

        Args:
            directory: Ruta del directorio a crear
        """
        try:
            os.makedirs(directory, exist_ok=True)
        except Exception as e:
            self.logger.error(f"No se pudo crear directorio {directory}: {e}")
            raise OSError(f"Error creando directorio: {directory}") from e

    def file_hash(self, filepath, chunk_size=8192):
        """Calcula el hash SHA-256 de un archivo.

        Args:
            filepath: Ruta al archivo

        Returns:
            str: Hash hexadecimal del archivo
        """
        sha256 = hashlib.sha256()
        try:
            with open(filepath, "rb") as f:
                while chunk := f.read(chunk_size):
                    sha256.update(chunk)
            return sha256.hexdigest()
        except Exception as e:
            self.logger.error(f"Error calculando hash: {e}")
            raise IntegrityError(f"Error verificando integridad de {filepath}") from e

    def safe_move(self, src: str, dst: str) -> None:
        """Mueve un archivo verificando integridad.

        Args:
            src: Ruta origen
            dst: Ruta destino

        Raises:
            IntegrityError: Si hay discrepancia en los hashes
            OSError: Para otros errores de sistema
        """
        try:
            # Verificar hash origen
            src_hash = self.file_hash(src)

            # Mover archivo
            shutil.move(src, dst)

            # Verificar hash destino
            if self.file_hash(dst) != src_hash:
                raise IntegrityError(f"Hash mismatch after moving {src}")
        except PermissionError as e:
            self.logger.error("Permiso Denegado")
            raise OSError(f"Permiso Denegado {e}")
        except shutil.Error as e:
            self.logger.error(f"Error moviendo {src} -> {dst}: {e}")
            raise OSError(f"Error moviendo archivo: {src}") from e
        except Exception as e:
            self.logger.error(f"Error inesperado {e}")

    def process_single_file(
        self,
        directory: str,
        filename: str,
        conflict_resolution: str = "rename",  # Options: "rename", "skip", "overwrite"
    ) -> Optional[Tuple[str, str]]:
        """
        Processes a single file with comprehensive validation and error handling.

        Args:
            directory: Base directory where the file is located
            filename: Name of the file to process
            conflict_resolution: Strategy for handling filename conflicts:
                - "rename": Add suffix to duplicate files
                - "skip": Keep both files (skip moving)
                - "overwrite": Replace existing file (dangerous)

        Returns:
            Tuple of (source_path, destination_path) if file was moved successfully,
            None if file was skipped or error occurred.

        Raises:
            OSError: For filesystem-related errors
            IntegrityError: For file validation failures
        """
        src_path = os.path.join(directory, filename)
        log_prefix = f"[Procesando {filename}]"

        try:
            # 1. Initial validations
            if not os.path.exists(src_path):
                self.logger.warning(f"{log_prefix} Archivo no encontrado, omitiendo")
                return None

            if os.path.isdir(src_path):
                self.logger.debug(f"{log_prefix} Es un directorio, omitiendo")
                return None

            # 2. Detailed file validation
            if not self.validate_file(src_path):
                self.logger.warning(f"{log_prefix} Falló validación, omitiendo")
                return None

            # 3. Calculate file hash for integrity verification
            original_hash = self.file_hash(src_path)
            self.logger.debug(f"{log_prefix} Hash calculado: {original_hash[:8]}...")

            # 4. Determine destination
            ext = os.path.splitext(filename)[1].lower()
            folder = self.profiles[self.current_profile]["formatos"].get(ext, "Otros")
            dest_dir = os.path.join(directory, folder)

            # 5. Create destination directory if needed
            if not os.path.exists(dest_dir):
                try:
                    os.makedirs(dest_dir, exist_ok=True)
                    self.logger.info(f"{log_prefix} Directorio creado: {dest_dir}")
                except OSError as e:
                    self.logger.error(f"{log_prefix} Error creando directorio: {e}")
                    raise

            # 6. Handle filename conflicts
            base_name, ext = os.path.splitext(filename)
            dest_path = os.path.join(dest_dir, filename)

            if os.path.exists(dest_path):
                if conflict_resolution == "skip":
                    self.logger.info(
                        f"{log_prefix} Archivo existe, omitiendo (conflict_resolution=skip)"
                    )
                    return None
                elif conflict_resolution == "overwrite":
                    if not os.access(dest_path, os.W_OK):
                        self.logger.warning(
                            f"{log_prefix} Sin permisos para sobrescribir, omitiendo"
                        )
                        return None
                    self.logger.warning(
                        f"{log_prefix} Sobrescribiendo archivo existente"
                    )
                else:  # rename (default)
                    counter = 1
                    while os.path.exists(dest_path):
                        new_name = f"{base_name}_{counter}{ext}"
                        dest_path = os.path.join(dest_dir, new_name)
                        counter += 1
                    self.logger.info(
                        f"{log_prefix} Renombrado a {os.path.basename(dest_path)} para evitar colisión"
                    )

            # 7. Move file with integrity check
            try:
                # First copy then verify (safer than direct move)
                temp_path = dest_path + ".tmp"
                shutil.copy2(src_path, temp_path)

                # Verify copied file
                if self.file_hash(temp_path) != original_hash:
                    os.remove(temp_path)
                    raise IntegrityError(
                        f"{log_prefix} Error de integridad después de copiar"
                    )

                # Rename temp to final name
                os.rename(temp_path, dest_path)

                # Remove original only after successful copy+verify
                os.remove(src_path)

                self.logger.info(f"{log_prefix} Movido exitosamente a {dest_path}")
                return (src_path, dest_path)

            except Exception as move_error:
                # Cleanup in case of partial failure
                if os.path.exists(temp_path):
                    try:
                        os.remove(temp_path)
                    except Exception as cleanup_error:
                        self.logger.error(
                            f"{log_prefix} Error limpiando archivo temporal: {cleanup_error}"
                        )

                self.logger.error(f"{log_prefix} Error moviendo archivo: {move_error}")
                raise

        except PermissionError as pe:
            self.logger.error(f"{log_prefix} Error de permisos: {pe}")
            self.update_ui_from_thread(
                lambda: messagebox.showwarning(
                    "Permiso Denegado", "No se pudo procesar )"
                )
            )
            return None

        except IntegrityError as ie:
            self.logger.error(f"{log_prefix} Error de integridad: {ie}")
            return None

        except OSError as ose:
            self.logger.error(f"{log_prefix} Error del sistema: {ose}")
            return None

        except Exception as e:
            self.logger.error(f"{log_prefix} Error inesperado: {e}", exc_info=True)
            return None

    def finalize_operation(self, moved_files):
        """Realiza acciones finales después de mover archivos"""
        if moved_files:
            self.log(f"Operación completada. Archivos movidos: {len(moved_files)}")
            self.update_ui_from_thread(lambda: setattr(self.progress, "values", 100))

    def update_ui_from_thread(self, callback):
        """Ejecuta una función en el hilo principal de la UI de forma segura.

        Args:
            callback: Función a ejecutar en el hilo principal
        """
        if not self.running:  # Verificar si la aplicación sigue activa
            return
        self.after(0, lambda: self._safe_execute(callback))

    def _safe_execute(self, callback):
        """Ejecuta el callback con manejo de errores"""
        try:
            if self.running:  # Doble verificación
                callback()
        except Exception as e:
            self.logger.error(f"Error en actualización de UI: {e}")

    def organize_files(self, directory: str) -> None:
        """Organiza los archivos en el directorio especificado según los formatos configurados.

        Args:
            directory: Ruta del directorio a organizar

        Raises:
            ValueError: Si el directorio no es válido
            OSError: Para errores de sistema de archivos
        """
        try:
            self.validate_directory(directory)
            self.logger.info(f"Iniciando organización en: {directory}")

            with ThreadPoolExecutor(max_workers=4) as executor:
                futures = [
                    executor.submit(self.process_single_file, directory, filename)
                    for filename in self.safe_listdir(directory)
                ]

                self.process_results(futures)

        except Exception as e:
            self.logger.error(f"Error en organize_files: {e}", exc_info=True)
            self.update_ui_from_thread(lambda: messagebox.showerror("Error"))

    def handle_uncaught_exception(self, exc_type, exc_value, exc_traceback):
        """Maneja excepciones no capturadas"""
        self.logger.critical(
            "Uncaught exception", exc_info=(exc_type, exc_value, exc_traceback)
        )
        messagebox.showerror(
            "Error Crítico",
            f"Ocurrió un error no manejado: {str(exc_value)}\nVer logs para detalles.",
        )

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

    def on_closing(self):
        """Cierre profesional con limpieza mejorada"""
        self.logger.info("Iniciando cierre de aplicación")
        self.running = False  # Señal global de parada

        try:
            # 1. Detener hilos (máximo 3 segundos de espera)
            if hasattr(self, "thread_manager"):
                self.thread_manager.stop_all(timeout=3)

            # 2. Guardar estado en segundo plano (con timeout)
            save_thread = threading.Thread(target=self.save_to_file, daemon=True)
            save_thread.start()
            save_thread.join(timeout=2)  # Espera 2 segundos

            self.logger.info("Aplicación cerrada correctamente")
        except Exception as e:
            self.logger.error(f"Error durante el cierre: {e}", exc_info=True)
            messagebox.showerror(
                "Error al cerrar",
                "No se pudieron guardar todos los datos. Verifique el log.",
            )
        finally:
            # 3. Forzar cierre incluso si hay errores
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
