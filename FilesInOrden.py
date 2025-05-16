import os
import sys
import time
import json
import logging
import threading
import subprocess
import hashlib
from datetime import datetime
from collections import deque
from queue import Queue, Empty
from typing import Dict, Optional, List, Tuple
from logging.handlers import RotatingFileHandler
from concurrent.futures import ThreadPoolExecutor, as_completed
from concurrent.futures import Future

# Tkinter y GUI
from tkinter import *
import tkinter as tk
from tkinter import (
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


class IntegrityError(Exception):
    """Excepción para errores de integridad de archivos con contexto adicional"""

    def __init__(
        self,
        message: str,
        filepath: str = None,
        expected_hash: str = None,
        actual_hash: str = None,
    ):
        """
        Args:
            message: Descripción del error
            filepath: Ruta del archivo problemático
            expected_hash: Hash esperado (opcional)
            actual_hash: Hash obtenido (opcional)
        """
        super().__init__(message)
        self.filepath = filepath
        self.expected_hash = expected_hash
        self.actual_hash = actual_hash
        self.timestamp = datetime.now().isoformat()

    def __str__(self):
        base_msg = super().__str__()
        details = []
        if self.filepath:
            details.append(f"Archivo: {self.filepath}")
        if self.expected_hash and self.actual_hash:
            details.append(f"Hash esperado: {self.expected_hash[:8]}...")
            details.append(f"Hash obtenido: {self.actual_hash[:8]}...")
        return f"{base_msg} ({'; '.join(details)})" if details else base_msg


class ThreadManager:
    def __init__(self):
        self.threads = {}
        self.lock = threading.Lock()
        self.stop_event = threading.Event()

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
    """
    Implementación profesional de tooltips para widgets Tkinter.

    Características:
    - Valores por defecto sensibles
    - Retardo configurable para aparición/desaparición
    - Soporte para formato de texto
    - Manejo seguro de eventos
    - Compatibilidad con temas

    Uso básico:
        ToolTip(widget, "Texto del tooltip")

    Uso avanzado:
        ToolTip(widget, text="Texto", bg="#ffffe0", fg="#000000",
               font=('Arial', 9), delay=500, wraplength=200)
    """

    def __init__(
        self, widget, text=None, bg=None, fg=None, font=None, delay=500, wraplength=200
    ):
        """
        Inicializa el tooltip.

        Args:
            widget: Widget al que se asociará el tooltip
            text: Texto a mostrar (puede contener \n para saltos de línea)
            bg: Color de fondo (default: sistema)
            fg: Color de texto (default: sistema)
            font: Fuente a usar (default: sistema)
            delay: Milisegundos antes de mostrar (default: 500ms)
            wraplength: Ancho máximo en píxeles antes de envolver texto
        """
        self.widget = widget
        self.text = text
        self.bg = bg
        self.fg = fg
        self.font = font
        self.delay = delay
        self.wraplength = wraplength
        self.tip_window = None
        self.id = None
        self.x = self.y = 0
        self._schedule_id = None
        self._hide_id = None

        # Establecer colores por defecto según el tema del sistema
        if bg is None:
            self.bg = "#ffffe0"  # Amarillo claro por defecto
        if fg is None:
            self.fg = "#000000"  # Negro por defecto
        if font is None:
            self.font = ("TkDefaultFont", 9)

        # Vincular eventos
        self.widget.bind("<Enter>", self._on_enter)
        self.widget.bind("<Leave>", self._on_leave)
        self.widget.bind("<ButtonPress>", self._on_leave)

    def _on_enter(self, event=None):
        """Programa la aparición del tooltip"""
        self._schedule_show()

    def _on_leave(self, event=None):
        """Oculta el tooltip inmediatamente"""
        self._unschedule()
        self.hide()

    def _schedule_show(self):
        """Programa la aparición del tooltip después del delay"""
        self._unschedule()
        self._schedule_id = self.widget.after(self.delay, self.show)

    def _unschedule(self):
        """Cancela cualquier aparición programada"""
        if self._schedule_id:
            self.widget.after_cancel(self._schedule_id)
            self._schedule_id = None
        if self._hide_id:
            self.widget.after_cancel(self._hide_id)
            self._hide_id = None

    def show(self, event=None):
        """Muestra el tooltip con formato profesional"""
        if self.tip_window or not self.text:
            return

        # Posicionamiento relativo al widget
        x, y, _, _ = self.widget.bbox("insert")
        x += self.widget.winfo_rootx() + 25
        y += self.widget.winfo_rooty() + 25

        # Crear ventana tooltip
        self.tip_window = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{x}+{y}")

        # Configurar etiqueta con texto
        label = tk.Label(
            tw,
            text=self.text,
            justify=tk.LEFT,
            background=self.bg,
            foreground=self.fg,
            relief=tk.SOLID,
            borderwidth=1,
            font=self.font,
            wraplength=self.wraplength,
            padx=4,
            pady=2,
        )
        label.grid(ipadx=1, ipady=1)

        # Actualizar posición si excede la pantalla
        self._adjust_position(tw)

    def _adjust_position(self, tip_window):
        """Ajusta la posición si el tooltip se sale de la pantalla"""
        screen_width = self.widget.winfo_screenwidth()
        screen_height = self.widget.winfo_screenheight()

        # Obtener dimensiones del tooltip (requiere actualización)
        tip_window.update_idletasks()
        width = tip_window.winfo_width()
        height = tip_window.winfo_height()

        # Ajustar coordenada x
        x, y = tip_window.winfo_x(), tip_window.winfo_y()
        if x + width > screen_width:
            x = screen_width - width - 5
        if x < 0:
            x = 5

        # Ajustar coordenada y
        if y + height > screen_height:
            y = screen_height - height - 5
        if y < 0:
            y = 5

        tip_window.wm_geometry(f"+{x}+{y}")

    def hide(self, event=None):
        """Oculta el tooltip con animación suave"""
        if self.tip_window:
            try:
                # Efecto de desvanecimiento opcional
                self._fade_out()
            except:
                # Fallback a ocultar inmediatamente si hay error
                self.tip_window.destroy()
                self.tip_window = None

    def _fade_out(self, alpha=1.0):
        """Efecto de desvanecimiento (opcional)"""
        if alpha <= 0:
            self.tip_window.destroy()
            self.tip_window = None
            return

        if self.tip_window:
            self.tip_window.attributes("-alpha", alpha)
            self._hide_id = self.widget.after(50, lambda: self._fade_out(alpha - 0.1))

    def update_text(self, new_text):
        """Actualiza el texto del tooltip dinámicamente"""
        self.text = new_text
        if self.tip_window:
            for child in self.tip_window.winfo_children():
                if isinstance(child, tk.Label):
                    child.config(text=new_text)
                    self._adjust_position(self.tip_window)

    def destroy(self):
        """Limpia todos los recursos del tooltip"""
        self._unschedule()
        self.hide()
        self.widget.unbind("<Enter>")
        self.widget.unbind("<Leave>")
        self.widget.unbind("<ButtonPress>")


class TextRedirector(object):
    """Clase para redirigir stdout/stderr al área de texto"""

    def __init__(self, widget, tag="stdout"):
        self.widget = widget
        self.tag = tag

    def write(self, str):
        self.widget.configure(state="normal")
        self.widget.insert("end", str, (self.tag,))
        self.widget.configure(state="disabled")
        self.widget.see("end")

    def flush(self):
        pass


class FileOrganizerGUI(tk.Tk):
    def __init__(self):
        super().__init__()

        # Configuración básica de la ventana
        self.title("Organizador de Archivos")
        self.geometry("900x700")
        # self.minsize(800, 600)
        self.configure(bg="#f0f0f0")

        # Configuración inicial
        self.setup_logging()
        self.logger.info("Inicializando aplicación")

        # Inicializar todos los atributos primero
        self.default_formats = {...}  # Tus formatos aquí
        self.current_profile = "default"
        self.profiles = {}
        self.task_queue = Queue(maxsize=100)
        self.running = True
        self.undo_stack = deque(maxlen=5)

        # Inicializar atributos de widgets como None
        self.main_container = None
        self.preview_tree = None  # ¡Importante! Inicializar como None

        # Configuración restante
        self.load_profiles()

        # Crear contenedor principal
        self.main_container = ttk.Frame(self)
        self.main_container.grid(row=0, column=0, sticky="nsew")

        # Configurar expansión
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=1)
        self.main_container.grid_rowconfigure(0, weight=1)
        self.main_container.grid_columnconfigure(0, weight=1)

        # Crear widgets
        self.create_widgets()  # Ahora preview_tree se creará aquí

        # Configuraciones finales
        self.setup_performance_optimizations()
        self.init_threads()

    def setup_responsive_behavior(self):
        # Bind para redimensionamiento
        self.bind("<Configure>", self.on_window_resize)

        # Lista de widgets que necesitan ajuste especial
        self.responsive_widgets = [
            (self.preview_tree, {"column": ["original", "destino"]}),
            (self.format_tree, {"column": ["ext", "folder"]}),
        ]

    def on_window_resize(self, event):
        # Ajustar proporciones de columnas
        win_width = self.winfo_width()

        for widget, config in self.responsive_widgets:
            if widget.winfo_exists():
                for col in config.get("column", []):
                    widget.column(col, width=int(win_width * 0.4))  # 40% del ancho

    def check_screen_size(self):
        # Ocultar/mostrar elementos según tamaño
        screen_width = self.winfo_width()

        if screen_width < 1000:
            # Modo compacto
            self.notebook.tab(1, state="normal" if screen_width > 800 else "hidden")
        else:
            # Modo normal
            self.notebook.tab(1, state="normal")

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
        if self.current_profile not in self.profiles:
            self.current_profile = "default"

        profile = self.profiles[self.current_profile]
        self.dir_entry.delete(0, END)
        self.dir_entry.insert(0, profile["directory"])
        self.schedule_combo.set(profile["schedule"])
        self.update_format_tree(profile["formatos"])

    def observador(self):
        messagebox.showinfo("Info", "Funcion automatica\nahun no esta terminada")

    def create_widgets(self):
        """
        Crea todos los widgets de la interfaz gráfica, organizados en pestañas y secciones.
        Incluye:
        - Barra de menú
        - Pestañas principales (Operaciones y Configuración)
        - Área de registro
        - Barra de estado
        """
        # Notebook principal (ahora dentro del contenedor)
        self.notebook = ttk.Notebook(self.main_container)
        self.notebook.grid(row=0, column=0, sticky="nsew")

        # Configurar expansión
        self.main_container.grid_rowconfigure(0, weight=1)
        self.main_container.grid_columnconfigure(0, weight=1)

        # Pestañas
        ops_tab = ttk.Frame(self.notebook)
        config_tab = ttk.Frame(self.notebook)

        # Configurar expansión en cada pestaña
        ops_tab.grid_rowconfigure(0, weight=1)
        ops_tab.grid_columnconfigure(0, weight=1)

        config_tab.grid_rowconfigure(0, weight=1)
        config_tab.grid_columnconfigure(0, weight=1)

        # Configuración de estilo avanzado
        self.style = ttk.Style()
        self.style.theme_use("clam")

        # Configurar colores según el tema
        self.setup_theme_system()

        # Frame principal con scroll
        main_frame = ttk.Frame(self, padding=10)
        main_frame.grid(row=0, column=0, sticky="nsew")

        # Sistema de pestañas
        self.notebook = ttk.Notebook(main_frame)
        self.notebook.grid(row=0, column=0, sticky="nsew")

        # ----------------------------
        # Pestaña de Operaciones
        # ----------------------------
        ops_tab = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(ops_tab, text="Operaciones")

        # Panel de directorio
        dir_frame = ttk.LabelFrame(ops_tab, text="Selección de Directorio", padding=10)
        dir_frame.grid(row=0, column=0, sticky="nsew")

        ttk.Label(dir_frame, text="Directorio a organizar:").grid(
            row=0, column=0, sticky="w"
        )
        self.dir_entry = ttk.Entry(dir_frame)
        self.dir_entry.grid(row=0, column=0, sticky="nsew")

        browse_btn = ttk.Button(
            dir_frame, text="Examinar", command=self.select_directory
        )
        browse_btn.grid(row=0, column=0, sticky="nsew")
        ToolTip(browse_btn, "Seleccione el directorio que desea organizar")

        # Panel de acciones
        action_frame = ttk.LabelFrame(ops_tab, text="Acciones", padding=10)
        action_frame.grid(row=0, column=0, sticky="nsew")

        btn_grid = ttk.Frame(action_frame)
        btn_grid.grid()

        buttons = [
            ("Previsualizar", self.preview_changes, 0, 0),
            ("Organizar", self.start_organization, 0, 1),
            ("Deshacer", self.undo_last, 0, 2),
            ("Observer", self.observador, 0, 3),
        ]

        for text, command, row, col in buttons:
            btn = ttk.Button(
                btn_grid, text=text, command=command, style="Accent.TButton"
            )
            btn.grid(row=row, column=col, padx=5, pady=5, sticky=tk.NSEW)
            ToolTip(btn, f"Ejecutar acción: {text}")

        # Panel de previsualización
        self.create_preview_tree(ops_tab)

        # Panel de progreso
        progress_frame = ttk.LabelFrame(ops_tab, text="Progreso", padding=10)
        progress_frame.grid(sticky=tk.EW)  # Expandir horizontalmente

        # Configurar la columna del frame para que se expanda
        ops_tab.grid_columnconfigure(0, weight=1)  # Asumiendo que es la columna 0

        self.progress = ttk.Progressbar(
            progress_frame, orient=tk.HORIZONTAL, mode="determinate", length=300
        )
        self.progress.grid(sticky=tk.EW, pady=5)  # Expandir horizontalmente

        # Configurar la columna del progress_frame para que se expanda
        progress_frame.grid_columnconfigure(0, weight=1)

        # ----------------------------
        # Pestaña de Configuración
        # ----------------------------
        config_tab = ttk.Frame(self.notebook, padding=10)
        self.notebook.add(config_tab, text="Configuración")

        # Subpestañas dentro de Configuración
        config_notebook = ttk.Notebook(config_tab)
        config_notebook.grid(row=0, column=0, sticky="nsew")

        # Subpestaña de Formatos
        format_tab = ttk.Frame(config_notebook, padding=10)
        self.build_format_settings(format_tab)
        config_notebook.add(format_tab, text="Formatos")

        # Subpestaña de Apariencia
        appearance_tab = ttk.Frame(config_notebook, padding=10)
        self.build_appearance_settings(appearance_tab)
        config_notebook.add(appearance_tab, text="Apariencia")

        # ----------------------------
        # Área de Registro (parte inferior)
        # ----------------------------
        # self.create_log_area(main_frame)  # Usa la función que definimos antes

        # ----------------------------
        # Barra de Estado
        # ----------------------------
        self.setup_status_bar(main_frame)

        # Configuración de estilo para botón destacado
        self.style.configure(
            "Accent.TButton",
            foreground="white",
            background="#0078d7",
            font=("Segoe UI", 9, "bold"),
        )

        self.style.map(
            "Accent.TButton",
            background=[("active", "#005fa3"), ("disabled", "#cccccc")],
        )

        # Asegurar que los grids se expandan correctamente
        btn_grid.columnconfigure(0, weight=1)
        btn_grid.columnconfigure(1, weight=1)

    def log(self, message, level="INFO"):
        """
        Escribe un mensaje en el área de registro.

        Args:
            message: Texto del mensaje
            level: Nivel de log (INFO, WARNING, ERROR, CRITICAL)
        """
        if not hasattr(self, "log_area"):
            return

        timestamp = datetime.now().strftime("%H:%M:%S")
        self.log_area.configure(state="normal")
        self.log_area.insert(tk.END, f"[{timestamp}] {message}\n", (level,))
        self.log_area.configure(state="disabled")
        self.log_area.see(tk.END)

    def create_preview_tree(self, parent):
        """
        Crea un Treeview para previsualizar los cambios de organización.

        Args:
            parent: Widget padre donde se ubicará el treeview
        """
        # Frame contenedor
        preview_frame = ttk.LabelFrame(
            parent, text="Previsualización de Cambios", padding=10
        )
        preview_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)

        parent.grid_rowconfigure(0, weight=1)
        parent.grid_columnconfigure(0, weight=1)
        preview_frame.grid_rowconfigure(0, weight=1)
        preview_frame.grid_columnconfigure(0, weight=1)

        # Treeview con scrollbars
        tree_container = ttk.Frame(preview_frame)
        tree_container.grid(
            row=0, column=0, sticky="nsew"
        )  # Corregí column=5 a column=0

        # Configurar scrollbars
        vsb = ttk.Scrollbar(tree_container, orient="vertical")
        hsb = ttk.Scrollbar(tree_container, orient="horizontal")

        # Crear el Treeview
        self.preview_tree = ttk.Treeview(
            tree_container,
            columns=("original", "destino", "estado"),
            show="headings",
            yscrollcommand=vsb.set,
            xscrollcommand=hsb.set,
            selectmode="extended",
            height=10,
        )

        # Configurar columnas (esto debe ir DESPUÉS de crear el Treeview)
        self.preview_tree.column("original", width=300, stretch=tk.YES)
        self.preview_tree.column("destino", width=300, stretch=tk.YES)
        self.preview_tree.column("estado", width=100, stretch=tk.NO)

        self.preview_tree.heading("original", text="Ubicación Original", anchor=tk.W)
        self.preview_tree.heading("destino", text="Nueva Ubicación", anchor=tk.W)
        self.preview_tree.heading("estado", text="Estado", anchor=tk.W)

        # Configurar scrollbars
        vsb.config(command=self.preview_tree.yview)
        hsb.config(command=self.preview_tree.xview)

        # Layout
        self.preview_tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")

        # Configurar el grid para expandirse
        tree_container.grid_rowconfigure(0, weight=1)
        tree_container.grid_columnconfigure(0, weight=1)

        # Context menu
        self._setup_preview_context_menu()

    def _setup_preview_context_menu(self):
        """Configura el menú contextual para el treeview de previsualización"""
        self.preview_menu = tk.Menu(self.preview_tree, tearoff=0)
        self.preview_menu.add_command(
            label="Copiar ubicación", command=lambda: self._copy_preview_location()
        )
        self.preview_menu.add_separator()
        self.preview_menu.add_command(
            label="Examinar archivo", command=lambda: self._explore_preview_file()
        )

        self.preview_tree.bind("<Button-3>", self._show_preview_context_menu)

    def _show_preview_context_menu(self, event):
        """Muestra el menú contextual en el treeview de previsualización"""
        item = self.preview_tree.identify_row(event.y)
        if item:
            self.preview_tree.selection_set(item)
            self.preview_menu.post(event.x_root, event.y_root)

    def _copy_preview_location(self):
        """Copia la ubicación del archivo seleccionado al portapapeles"""
        selected = self.preview_tree.selection()
        if selected:
            values = self.preview_tree.item(selected[0], "values")
            self.clipboard_clear()
            self.clipboard_append(values[1])  # Copia la ubicación destino
            self.log("Ubicación copiada al portapapeles")

    def _explore_preview_file(self):
        """Abre el explorador de archivos en la ubicación del archivo seleccionado"""
        selected = self.preview_tree.selection()
        if selected:
            values = self.preview_tree.item(selected[0], "values")
            path = values[1]  # Ubicación destino

            if os.name == "nt":  # Windows
                os.startfile(os.path.dirname(path))
            elif os.name == "posix":  # Linux, Mac
                subprocess.run(["xdg-open", os.path.dirname(path)])

    def select_directory(self):
        directory = filedialog.askdirectory(title="Seleccionar carpeta a organizar")
        if directory:  # Si el usuario no cancela
            self.dir_entry.delete(0, tk.END)
            self.dir_entry.insert(0, directory)

    def build_operations_tab(self, parent):
        """Versión compacta similar al ejemplo"""
        # Configuración de directorio
        dir_frame = ttk.LabelFrame(parent, text="Directorio")
        dir_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)

        self.dir_entry = ttk.Entry(dir_frame)
        self.dir_entry.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)

        ttk.Button(dir_frame, text="Examinar", command=self.select_directory).grid(
            row=0, column=0, sticky="nsew"
        )

        # Panel de acciones
        action_frame = ttk.LabelFrame(
            parent,
            text="Acciones",
            padding=5,  # Añadir padding interno para mejor espaciado
        )
        action_frame.grid(
            row=0,
            column=0,
            sticky="nsew",  # Expandir en todas direcciones
            padx=5,
            pady=5,
            ipadx=5,  # Padding interno horizontal
            ipady=5,  # Padding interno vertical
        )

        # Configurar expansión del frame padre
        parent.grid_rowconfigure(0, weight=0)  # Sin expansión vertical (altura fija)
        parent.grid_columnconfigure(0, weight=1)  # Expansión horizontal completa

        # Contenedor grid para los botones
        btn_grid = ttk.Frame(action_frame)
        btn_grid.grid(
            row=0,
            column=0,
            sticky="nsew",  # Expandir dentro del frame
            padx=2,  # Pequeño margen interno
            pady=2,
        )

        # Configurar expansión del grid de botones
        action_frame.grid_rowconfigure(0, weight=1)
        action_frame.grid_columnconfigure(0, weight=1)

        # Configurar columnas del btn_grid (ajustar según número de botones)
        for col in range(4):  # Ejemplo para 4 columnas
            btn_grid.grid_columnconfigure(
                col, weight=1, uniform="btns"
            )  # Mismo ancho para todos

        # Barra de progreso
        self.progress = ttk.Progressbar(
            parent, orient=tk.HORIZONTAL, mode="determinate"
        )
        self.progress.grid(row=0, column=0, sticky="nsew", padx=10, pady=5)

        parent.grid_rowconfigure(2, weight=1)
        # La fila 2 puede ser la que contiene el treeview
        parent.grid_columnconfigure(0, weight=1)

    def build_config_tab(self, parent):
        # Configurar peso de filas/columnas
        parent.grid_rowconfigure(0, weight=1)
        parent.grid_columnconfigure(0, weight=1)

        config_notebook = ttk.Notebook(parent)
        config_notebook.grid(row=0, column=0, sticky="nsew")

    def remove_format(self):
        selected = self.format_tree.selection()
        if selected:
            values = self.format_tree.item(selected[0])
            self.profiles["default"]["formatos"].pop(values["values"][0])
            self.log(self.profiles["default"]["formatos"])
            self.format_tree.delete(selected[0])

    def apply_appearance_settings(self):
        """Aplica todos los cambios de apariencia"""
        self.change_theme()
        # self.update_font_settings()
        messagebox.showinfo("Éxito", "Configuración de apariencia aplicada")

    def build_appearance_settings(self, parent):
        """
        Construye el panel de configuración de apariencia.
        Incluye:
        - Selección de tema
        - Configuración de fuentes
        - Opciones de visualización
        """
        # Frame principal
        main_frame = ttk.Frame(parent)
        main_frame.grid(row=0, column=0)

        # Sección de tema visual
        theme_frame = ttk.LabelFrame(main_frame, text="Tema Visual", padding=10)
        theme_frame.grid(row=0, column=0, sticky="nsew")

        ttk.Label(theme_frame, text="Estilo:").grid(row=0, column=0, sticky="e", padx=5)
        self.theme_combo = ttk.Combobox(
            theme_frame,
            values=["Claro", "Oscuro", "Profesional"],
            state="readonly",
        )
        self.theme_combo.grid(row=0, column=1, sticky="ew", padx=5, pady=5)
        self.theme_combo.set("Profesional")
        self.theme_combo.bind("<<ComboboxSelected>>", self.change_theme)

        options_frame = ttk.LabelFrame(main_frame, text="Opciones Visuales", padding=10)
        options_frame.grid(row=0, column=0, sticky="nsew")

        theme_frame.columnconfigure(1, weight=1)

    # NOTE: Añadir funcionlidad para clic derecho
    def build_format_settings(self, parent):
        """
        Construye el panel de configuración de formatos con:
        - Lista editable de extensiones y carpetas destino
        - Búsqueda/filtrado
        - Importación/exportación de configuraciones
        """
        main_frame = ttk.Frame(parent)
        main_frame.grid(row=0, column=0, sticky="nsew")
        main_frame.grid_rowconfigure(0, weight=0)
        main_frame.grid_rowconfigure(0, weight=1)
        # La barra de búsqueda no necesita expandirse verticalmente
        main_frame.grid_columnconfigure(0, weight=1)
        # Expansión horizontal completa

        # Barra de búsqueda
        search_frame = ttk.Frame(main_frame)
        search_frame.grid(row=0, column=0, sticky="ew", pady=5)
        search_frame.grid_rowconfigure(0, weight=0)
        # La barra de búsqueda no necesita expandirse verticalmente
        search_frame.grid_columnconfigure(0, weight=1)
        # Expansión horizontal completa

        ttk.Label(search_frame, text="Buscar:").grid(row=0, sticky="w", padx=(0, 5))
        self.search_entry = ttk.Entry(search_frame)
        self.search_entry.grid(row=0, column=1, sticky="ew", padx=(0, 5))
        self.search_entry.bind("<KeyRelease>", self.filter_formats)

        # Treeview de formatos
        tree_frame = ttk.Frame(main_frame)
        tree_frame.grid(row=0, column=0, sticky="nsew")

        # Configurar scrollbars
        vsb = ttk.Scrollbar(tree_frame, orient="vertical")
        # hsb = ttk.Scrollbar(tree_frame, orient="horizontal")

        # Crear el Treeview
        self.format_tree = ttk.Treeview(
            tree_frame,
            columns=("ext", "folder"),
            show="headings",
            yscrollcommand=vsb.set,
            # xscrollcommand=hsb.set,
            selectmode="browse",
            height=10,
        )

        # Configurar columnas
        self.format_tree.heading("ext", text="Extensión", anchor=tk.W)
        self.format_tree.heading("folder", text="Carpeta Destino", anchor=tk.W)
        self.format_tree.column("ext", width=120, stretch=tk.NO)
        self.format_tree.column("folder", width=250, stretch=tk.YES)

        # Configurar scrollbars
        vsb.config(command=self.format_tree.yview)
        # hsb.config(command=self.format_tree.xview)

        # Layout
        self.format_tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        # hsb.grid(row=1, column=0, sticky="ew")

        # Configurar el grid para expandirse
        tree_frame.grid_rowconfigure(0, weight=1)
        tree_frame.grid_columnconfigure(0, weight=1)

        # Controles de formatos
        ctrl_frame = ttk.Frame(main_frame)
        ctrl_frame.grid(row=0, column=0, sticky="nsew")

        control_buttons = [
            ("Agregar", self.add_format),
            ("Editar", self.edit_format),
            ("Eliminar", self.remove_format),
        ]

        for text, command in control_buttons:
            btn = ttk.Button(
                ctrl_frame, text=text, command=command, style="Small.TButton"
            )
            btn.grid(row=0, column=0, sticky="nsew")

        # Cargar formatos actuales
        self.update_format_tree(self.profiles[self.current_profile].get("formatos", {}))

    def _save_new_format(self, dialog, ext, folder):
        """Guarda el nuevo formato validado"""
        if not ext.startswith("."):
            ext = f".{ext}"

        ext = ext.lower().strip()
        folder = folder.strip()

        if not ext or not folder:
            messagebox.showwarning("Campos vacíos", "Ambos campos son requeridos")
            return

        # Verificar si la extensión ya existe
        for child in self.format_tree.get_children():
            existing_ext = self.format_tree.item(child)["values"][0]
            if existing_ext == ext:
                messagebox.showwarning(
                    "Extensión existente", f"La extensión {ext} ya está configurada"
                )
                return

        self.format_tree.insert("", tk.END, values=(ext, folder))
        dialog.destroy()

    def change_theme(self, event=None):
        """
        Cambia el tema visual de toda la aplicación basado en la selección del usuario.
        Maneja temas claros, oscuros y profesionales con configuración completa de estilos.

        Args:
            event: Parámetro opcional para manejar eventos de tkinter (como selección en combobox)
        """
        try:
            # Mapeo de nombres de temas a configuraciones internas
            theme_mapping = {
                "Claro": {
                    "style": "light",
                    "colors": {
                        "primary": "#f0f0f0",
                        "secondary": "#ffffff",
                        "text": "#000000",
                        "accent": "#0078d7",
                        "highlight": "#e1e1e1",
                    },
                },
                "Oscuro": {
                    "style": "dark",
                    "colors": {
                        "primary": "#2d2d2d",
                        "secondary": "#3d3d3d",
                        "text": "#ffffff",
                        "accent": "#0e639c",
                        "highlight": "#4d4d4d",
                    },
                },
                "Profesional": {
                    "style": "professional",
                    "colors": {
                        "primary": "#f5f5f5",
                        "secondary": "#e0e0e0",
                        "text": "#212121",
                        "accent": "#607d8b",
                        "highlight": "#d0d0d0",
                    },
                },
                "Sistema": {
                    "style": "clam",
                    "colors": {
                        "primary": "default",
                        "secondary": "default",
                        "text": "default",
                        "accent": "default",
                        "highlight": "default",
                    },
                },
            }

            selected_theme = self.theme_combo.get()
            theme_config = theme_mapping.get(
                selected_theme, theme_mapping["Profesional"]
            )

            # 1. Aplicar estilo ttk principal
            self.style.theme_use(theme_config["style"])

            # 2. Configurar colores base para todos los widgets
            self.style.configure(
                ".",
                background=theme_config["colors"]["primary"],
                foreground=theme_config["colors"]["text"],
                fieldbackground=theme_config["colors"]["primary"],
                selectbackground=theme_config["colors"]["accent"],
                selectforeground="white",
            )

            # 3. Configuración específica para widgets importantes
            self.style.configure("TFrame", background=theme_config["colors"]["primary"])

            self.style.configure(
                "TLabel",
                background=theme_config["colors"]["primary"],
                foreground=theme_config["colors"]["text"],
                font=("Segoe UI", 10),
            )

            self.style.configure(
                "TButton",
                background=theme_config["colors"]["accent"],
                foreground="white",
                font=("Segoe UI", 9),
                borderwidth=1,
                relief="raised",
            )

            self.style.map(
                "TButton",
                background=[
                    ("active", theme_config["colors"]["accent"]),
                    ("disabled", theme_config["colors"]["highlight"]),
                ],
            )

            # 4. Configuración especial para Treeviews
            self.style.configure(
                "Treeview",
                background=theme_config["colors"]["secondary"],
                foreground=theme_config["colors"]["text"],
                fieldbackground=theme_config["colors"]["secondary"],
                rowheight=25,
            )

            self.style.map(
                "Treeview",
                background=[("selected", theme_config["colors"]["accent"])],
                foreground=[("selected", "white")],
            )

            # 5. Actualizar widgets no-ttk (como el área de texto del log)
            self.log_area.configure(
                bg=theme_config["colors"]["secondary"],
                fg=theme_config["colors"]["text"],
                insertbackground=theme_config["colors"]["text"],
            )

            # 6. Actualizar ventana principal
            self.configure(background=theme_config["colors"]["primary"])

            # 7. Registrar cambio
            self.logger.info(f"Tema cambiado a: {selected_theme}")
            self.log(f"Tema visual actualizado a {selected_theme}")

        except Exception as e:
            self.logger.error(f"Error cambiando tema: {e}", exc_info=True)
            messagebox.showerror(
                "Error de Tema", f"No se pudo aplicar el tema seleccionado:\n{str(e)}"
            )

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
        self.status_bar.grid(row=0, column=0, sticky="nsew")

        # Componentes de la barra
        self.status_label = ttk.Label(
            self.status_bar, text="Listo", anchor=tk.W, style="Status.TLabel"
        )
        self.status_label.grid(row=0, column=0, sticky="nsew")

        self.memory_usage = ttk.Label(self.status_bar, text="RAM: 0MB", anchor=tk.E)
        self.memory_usage.grid(row=0)

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
        profile_path = os.path.abspath("profiles.json")  # Usar ruta absoluta
        self.logger.info(f"Guardando perfil en: {profile_path}")
        with open(profile_path, "w") as f:
            json.dump(self.profiles, f)

    def edit_format(self):
        pass

    def center_window(self, window):
        """Centra una ventana secundaria respecto a la ventana principal"""
        window.update_idletasks()
        width = window.winfo_width()
        height = window.winfo_height()

        x = (self.winfo_screenwidth() // 2) - (width // 2)
        y = (self.winfo_screenheight() // 2) - (height // 2)

        window.geometry(f"{width}x{height}+{x}+{y}")

    def add_format(self):
        """
        Muestra un diálogo para agregar un nuevo formato de archivo y su carpeta destino.

        Crea una ventana emergente con campos para:
        - Extensión del archivo (ej: .jpg)
        - Carpeta destino donde se moverán los archivos con esta extensión

        Al guardar, el nuevo formato se añade al Treeview y al perfil actual.

        Ejemplo de uso:
            self.add_format()  # Muestra el diálogo de agregar formato
        """

        def save_new_format():
            """
            Guarda el nuevo formato validando los campos y actualizando las estructuras de datos.

            Acciones:
            1. Obtiene y limpia los valores de los campos
            2. Valida que ambos campos contengan datos
            3. Añade el formato al Treeview
            4. Actualiza el diccionario de formatos en el perfil actual
            5. Cierra la ventana de diálogo
            """
            # Obtener y limpiar los valores
            ext = ext_entry.get().strip()
            folder = folder_entry.get().strip()

            # Validar que ambos campos tengan contenido
            if ext and folder:
                # Asegurar que la extensión comience con punto
                if not ext.startswith("."):
                    ext = f".{ext}"

                # Añadir al Treeview
                self.format_tree.insert("", END, values=(ext.lower(), folder))

                # Actualizar el diccionario de formatos
                self.profiles["default"]["formatos"][ext.lower()] = folder

                # Cerrar la ventana
                top.destroy()

        # Crear ventana emergente
        top = Toplevel(self)
        top.title("Agregar Formato")
        top.transient(self)  # Establecer como ventana hija
        top.grab_set()  # Modal

        # Configuración del sistema de grid
        top.grid_columnconfigure(0, weight=1)  # Columna principal expandible
        for i in range(5):  # Configurar 5 filas
            top.grid_rowconfigure(i, weight=1 if i == 4 else 0)

        # 1. Etiqueta y campo para extensión
        ttk.Label(top, text="Extensión (ej. .jpg, .png):", font=("Segoe UI", 9)).grid(
            row=0, column=0, padx=15, pady=(10, 2), sticky="w"
        )

        ext_entry = ttk.Entry(top, font=("Segoe UI", 9))
        ext_entry.grid(row=1, column=0, padx=15, pady=2, sticky="ew")

        # 2. Etiqueta y campo para carpeta destino
        ttk.Label(top, text="Carpeta destino:", font=("Segoe UI", 9)).grid(
            row=2, column=0, padx=15, pady=(10, 2), sticky="w"
        )

        folder_entry = ttk.Entry(top, font=("Segoe UI", 9))
        folder_entry.grid(row=3, column=0, padx=15, pady=2, sticky="ew")

        # 3. Botón de guardar
        btn_guardar = ttk.Button(
            top, text="Guardar", command=save_new_format, style="Accent.TButton"
        )
        btn_guardar.grid(row=4, column=0, padx=15, pady=(10, 15), sticky="ew")

        # Configuración adicional de la ventana
        top.resizable(False, False)  # No redimensionable
        top.bind("<Return>", lambda e: save_new_format())  # Enter para guardar
        ext_entry.focus_set()  # Foco inicial en el primer campo

        # Centrar la ventana respecto a la principal
        self.center_window(top)

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

    def build_preview_panel(self, parent):
        """
        Construye el panel de previsualización con Treeview y área de registro.
        Usa grid() para manejar la geometría de manera consistente.

        Args:
            parent: Widget padre donde se ubicará el panel
        """
        # Frame principal que contendrá ambos paneles (previsualización y registro)
        main_frame = ttk.Frame(parent)
        main_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)

        # Configurar expansión del frame principal
        parent.grid_rowconfigure(0, weight=1)
        parent.grid_columnconfigure(0, weight=1)
        main_frame.grid_rowconfigure(1, weight=1)  # La fila 1 será el área de registro
        main_frame.grid_columnconfigure(0, weight=1)

        # 1. Panel de previsualización (Treeview)
        preview_frame = ttk.LabelFrame(
            main_frame, text="Previsualización de Cambios", padding=5
        )
        preview_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=(0, 5))

        # Configurar Treeview con scrollbars
        self.preview_tree = ttk.Treeview(
            preview_frame,
            columns=("original", "destino", "estado"),
            show="headings",
            height=8,
        )

        # Configurar columnas
        self.preview_tree.column("original", width=300, stretch=True)
        self.preview_tree.column("destino", width=300, stretch=True)
        self.preview_tree.column("estado", width=100, stretch=False)

        self.preview_tree.heading("original", text="Ubicación Original", anchor=tk.W)
        self.preview_tree.heading("destino", text="Nueva Ubicación", anchor=tk.W)
        self.preview_tree.heading("estado", text="Estado", anchor=tk.W)

        # Scrollbars
        vsb = ttk.Scrollbar(
            preview_frame, orient="vertical", command=self.preview_tree.yview
        )
        hsb = ttk.Scrollbar(
            preview_frame, orient="horizontal", command=self.preview_tree.xview
        )
        self.preview_tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)

        # Layout del Treeview y scrollbars usando grid
        self.preview_tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")

        # Configurar expansión
        preview_frame.grid_rowconfigure(0, weight=1)
        preview_frame.grid_columnconfigure(0, weight=1)

        # 2. Área de registro
        log_frame = ttk.LabelFrame(
            main_frame, text="Registro de Actividades", padding=5
        )
        log_frame.grid(row=1, column=0, sticky="nsew", padx=5, pady=5)

        # Área de texto con scroll
        self.log_area = scrolledtext.ScrolledText(
            log_frame, wrap=tk.WORD, font=("Consolas", 9), height=10
        )
        self.log_area.grid(row=0, column=0, sticky="nsew")

        # Configurar tags para diferentes niveles de log
        self.log_area.tag_config("INFO", foreground="black")
        self.log_area.tag_config("WARNING", foreground="orange")
        self.log_area.tag_config("ERROR", foreground="red")
        self.log_area.tag_config("CRITICAL", foreground="red", background="yellow")

        # Configurar estado inicial del área de log
        self.log_area.configure(state="disabled")

        # Configurar expansión
        log_frame.grid_rowconfigure(0, weight=1)
        log_frame.grid_columnconfigure(0, weight=1)

        # Redirigir stdout y stderr al log
        sys.stdout = TextRedirector(self.log_area, "stdout")
        sys.stderr = TextRedirector(self.log_area, "stderr")

        # Context menu para el Treeview
        self._setup_preview_context_menu()

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

        # Solo configurar log_area si existe
        if hasattr(self, "log_area"):
            self.log_area.configure(bg=bg, fg=fg, insertbackground=fg)

        # Actualizar otros widgets si es necesario
        if hasattr(self, "format_tree"):
            self.format_tree.update_idletasks()
        if hasattr(self, "preview_tree"):
            self.preview_tree.update_idletasks()
        if hasattr(self, "preview_tree"):
            self.update_idletasks()

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

    def setup_animations(self):
        """Configura animaciones fluidas para transiciones de UI"""
        self.animation_queue = Queue()
        self.animation_running = False

        # Estilos de animación predefinidos
        self.animation_presets = {
            "fade": {"duration": 300, "steps": 10},
            "slide": {"duration": 200, "steps": 15},
            "highlight": {"duration": 150, "steps": 5},
        }

        def _process_animations():
            while self.running:
                try:
                    widget, anim_type, kwargs = self.animation_queue.get(timeout=0.1)
                    preset = self.animation_presets.get(anim_type, {})

                    # Fusionar configuración
                    config = {**preset, **kwargs}
                    self._execute_animation(widget, config)

                except Empty:
                    continue
                except Exception as e:
                    self.logger.error(f"Error en prosess animations {e}")

        # Hilo para procesar animaciones
        threading.Thread(
            target=_process_animations, name="AnimationThread", daemon=True
        ).start()

    def _execute_animation(self, widget, config):
        """Ejecuta una animación individual"""
        try:
            if config.get("type") == "fade":
                self._animate_fade(widget, **config)
            elif config.get("type") == "slide":
                self._animate_slide(widget, **config)

        except Exception as e:
            self.logger.error(f"Error en ejecutar animación: {e}")

    def _animate_fade(self, widget, duration=300, steps=10, **kwargs):
        """Efecto de desvanecimiento"""
        delta = 1.0 / steps
        delay = duration // steps

        for i in range(steps + 1):
            if not widget.winfo_exists():
                break
            alpha = 1.0 - (i * delta)
            try:
                widget.attributes("-alpha", alpha)
                widget.update()
                time.sleep(delay / 1000)
            except Exception as e:
                self.logger.error(f"Error: animation fade {e}")
                break

    def _animate_slide(self, widget, **config):
        messagebox.showinfo("Info", "Lo siento ahun no implementado")

    def setup_statusbar(self):
        """
        Configura una barra de estado avanzada con múltiples secciones usando grid().

        La barra de estado contiene:
        - Estado actual de la aplicación
        - Progreso de operaciones
        - Estadísticas de archivos procesados
        - Uso de memoria RAM
        - Hora actual

        Estructura:
            [Estado: texto] [Progreso: indicador] [Estadísticas: conteo] [RAM: uso] [Hora]

        Actualización:
        - Se actualiza automáticamente cada segundo mediante update_statusbar()
        """
        # Crear frame principal para la barra de estado
        self.status_bar = ttk.Frame(
            self,
            relief=tk.SUNKEN,
            padding=(5, 2, 5, 2),  # Padding uniforme (left, top, right, bottom)
            style="Statusbar.TFrame",
        )

        self.status_bar.grid(
            row=100,  # Fila inferior (número alto para asegurar posición)
            column=0,
            sticky="nsew",
            columnspan=100,  # Para ocupar todo el ancho
        )

        # Configurar expansión (asegurar que ocupe todo el ancho)
        self.grid_rowconfigure(100, weight=0)  # Sin expansión vertical
        self.grid_columnconfigure(0, weight=1)  # Expansión horizontal

        # Definición de secciones (más ordenada)
        sections = [
            # (name,        text,       width,  anchor,    stretch)
            ("status", "Listo", 30, tk.W, True),
            ("progress", "", 15, tk.CENTER, False),
            ("stats", "Archivos: 0", 20, tk.E, False),
            ("memory", "RAM: 0MB", 15, tk.E, False),
            ("time", "", 10, tk.E, False),
        ]

        # Configurar grid para las secciones
        self.status_bar.grid_columnconfigure(len(sections) - 1, weight=1)

        # Crear labels para cada sección
        self.status_labels = {}
        for col, (name, text, width, anchor, stretch) in enumerate(sections):
            # Configurar peso de columna
            if stretch:
                self.status_bar.grid_columnconfigure(col, weight=1)

            # Frame contenedor
            frame = ttk.Frame(self.status_bar, padding=(2, 0))
            frame.grid(row=0, column=col, sticky="nsew", padx=(0, 5))

            # Label del nombre
            ttk.Label(frame, text=f"{name.title()}:", style="Statusbar.TLabel").grid(
                row=0, column=0, sticky="w"
            )

            # Label del valor
            label = ttk.Label(
                frame, text=text, width=width, anchor=anchor, style="Statusbar.TLabel"
            )
            label.grid(row=0, column=1, sticky="ew")

            self.status_labels[name] = label

        # Configurar estilos (debe estar definido en tu aplicación)
        self.style.configure("Statusbar.TFrame", background="#f0f0f0", borderwidth=1)

        self.style.configure(
            "Statusbar.TLabel",
            background="#f0f0f0",
            font=("Segoe UI", 8),
            padding=(0, 0),
        )

        # Iniciar actualización periódica
        self.update_statusbar()

    def update_statusbar(self):
        """
        Actualiza dinámicamente los valores de la barra de estado.

        Se ejecuta automáticamente cada segundo y muestra:
        - Uso actual de memoria RAM
        - Hora del sistema
        - Conteo de hilos activos
        - Estado de la cola de tareas
        """
        try:
            # Actualizar uso de memoria
            mem = psutil.Process(os.getpid()).memory_info().rss / 1024 / 1024
            self.status_labels["memory"].config(text=f"RAM: {mem:.1f}MB")

            # Actualizar hora
            self.status_labels["time"].config(text=datetime.now().strftime("%H:%M:%S"))

            # Actualizar estadísticas del sistema
            threads = threading.active_count()
            tasks = self.task_queue.qsize()
            self.status_labels["stats"].config(
                text=f"Hilos: {threads} | Tareas: {tasks}"
            )

        except Exception as e:
            self.logger.error(f"Error actualizando barra de estado: {e}")

        # Programar próxima actualización
        self.after(1000, self.update_statusbar)

    def set_status(self, message: str, section="status", temporary=False):
        """Establece un mensaje en la barra de estado"""
        self.status_labels[section].config(text=message)

        if temporary:
            self.after(
                5000,
                lambda: self.status_labels[section].config(
                    text=self.status_defaults.get(section, "")
                ),
            )

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
                bg="blue",
                fg="black",
                font=("Arial", 9),
            ),
            "undo_button": ToolTip(
                self.undo_last,
                text="<b>Deshacer</b><br>Revierte la última operación realizada",
                bg="blue",
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
        if interval == "5 minutos":
            schedule.every(5).minutes.do(self.start_organization)
        elif interval == "1 hora":
            schedule.every().hour.do(self.start_organization)
        elif interval == "Diario":
            schedule.every().day.do(self.start_organization)

    def preview_changes(self):
        """Muestra una previsualización de los cambios con íconos"""
        # Limpiar el treeview
        self.preview_tree.delete(*self.preview_tree.get_children())

        # Obtener directorio seleccionado
        directory = self.dir_entry.get()

        # Validar directorio
        if not directory or not os.path.isdir(directory):
            self.log("Directorio no válido o no seleccionado", "ERROR")
            return

        try:
            # Procesar cada archivo en el directorio
            for filename in os.listdir(directory):
                src_path = os.path.join(directory, filename)

                if os.path.isfile(src_path):
                    # Procesar archivo
                    ext = os.path.splitext(filename)[1].lower()
                    folder = self.profiles[self.current_profile]["formatos"].get(
                        ext, "Otros"
                    )
                    dest_path = os.path.join(directory, folder, filename)

                    # Insertar en el treeview
                    self.preview_tree.insert(
                        "",
                        "end",
                        values=(src_path, dest_path, "Pendiente"),
                        tags=(ext,),
                    )

                elif os.path.isdir(src_path):
                    # Procesar directorio (no lo movemos, solo mostramos)
                    self.preview_tree.insert(
                        "",
                        "end",
                        values=(src_path, src_path, "Directorio"),
                        tags=("folder",),
                    )

        except Exception as e:
            self.log(f"Error al generar previsualización: {str(e)}", "ERROR")
            messagebox.showerror(
                "Error", f"No se pudo generar la previsualización:\n{str(e)}"
            )

    def start_organization(self):
        directory = self.dir_entry.get()
        if not directory:
            messagebox.showerror("Error", "Seleccione un directorio primero")
            self.log("Seleccione un directorio primero")
            return

        thread = threading.Thread(
            target=self.organize_files, args=(directory,), daemon=True
        )
        thread.start()

    def validate_directory(self, directory):
        if not os.path.isdir(directory):
            self.logger.error(f"Directorio no válido: {directory}")
            self.log(f"Directorio no válido: {directory}")
            raise ValueError(f"Directorio no válido: {directory}")
        if not os.access(directory, os.R_OK | os.W_OK):
            self.logger.error(f"Sin permisos en: {directory}")
            self.log(f"Sin permisos en: {directory}")
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
            self.log(f"Error leyendo directorio {directory}: {e}")
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

        self.log(message)
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
                self.log(f"Error procesando archivo: {e}")
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
                self.log(f"La ruta no es un archivo: {src_path}")
                self.logger.warning(f"La ruta no es un archivo: {src_path}")
                return False

            # 2. Verificar permisos de lectura
            if not os.access(src_path, os.R_OK):
                self.log(f"Sin permisos de lectura: {src_path}")
                self.logger.error(f"Sin permisos de lectura: {src_path}")
                raise PermissionError(f"No se puede leer el archivo: {src_path}")

            # 3. Verificar que el archivo no esté en uso (Multiplataforma)
            if os.name == "nt":  # Windows
                # Intento de apertura exclusiva
                with open(src_path, "rb+") as f:
                    pass
            else:  # Linux/macOS
                # Usar lsof para verificar si el archivo está abierto
                result = subprocess.run(
                    ["lsof", src_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE
                )
                if result.returncode == 0:
                    self.log(f"Archivo en uso (Linux): {src_path}")
                    self.logger.warning(f"Archivo en uso (Linux): {src_path}")
                    return False

            # 4. Verificar que no sea un archivo del sistema/protegido
            filename = os.path.basename(src_path)
            if filename.startswith(("~$", "Thumbs.db", ".DS_Store", "desktop.ini")):
                self.log(f"Ignorando archivo del sistema: {filename}")
                self.logger.debug(f"Ignorando archivo del sistema: {filename}")
                return False

            # 5. Verificar tamaño mínimo/máximo (opcional)
            file_size = os.path.getsize(src_path)
            if file_size == 0:
                self.log(f"Archivo vacío: {src_path}")
                self.logger.warning(f"Archivo vacío: {src_path}")
                return False
            if file_size > 100 * 1024 * 1024:  # 100MB
                self.log(f"Archivo demasiado grande (>100MB): {src_path}")
                self.logger.warning(f"Archivo demasiado grande (>100MB): {src_path}")
                return False

            # 6. Verificar extensión válida (opcional)
            ext = os.path.splitext(filename)[1].lower()
            if ext not in self.profiles[self.current_profile]["formatos"]:
                self.log(f"Extensión no configurada: {ext} en {filename}")
                self.logger.debug(f"Extensión no configurada: {ext} en {filename}")
                # No retornamos False aquí porque queremos permitir la categoría "Otros"

            # 7. Verificar integridad básica (para ciertos tipos de archivos)
            if ext in (".jpg", ".png", ".pdf", ".docx"):
                if not self._validate_file_signature(src_path, ext):
                    self.log(f"Firma de archivo inválida: {src_path}")
                    self.logger.error(f"Firma de archivo inválida: {src_path}")
                    raise IntegrityError(f"Archivo corrupto o inválido: {src_path}")

            return True

        except (IOError, PermissionError, FileNotFoundError):
            return False
        except Exception as e:
            self.log(f"Error verificando uso del archivo: {e}")
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
    try:
        app = FileOrganizerGUI()
        app.protocol("WM_DELETE_WINDOW", app.on_closing)
        app.mainloop()
    except Exception as e:
        print(f"Error fatal: {e}")
        # Podrías registrar esto en un archivo de log
