import os
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


class FileOrganizerGUI(tk.Tk):
    def __init__(self):
        super().__init__()
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

    def select_directory(self):
        directory = filedialog.askdirectory(title="Seleccionar carpeta a organizar")
        if directory:  # Si el usuario no cancela
            self.dir_entry.delete(0, tk.END)
            self.dir_entry.insert(0, directory)

    def create_widgets(self):
        # Configurar estilo
        self.style = ttk.Style()
        self.style.theme_use("clam")

        # Paneles principales
        main_panel = ttk.PanedWindow(self, orient=HORIZONTAL)
        main_panel.pack(fill=BOTH, expand=True)

        # Panel izquierdo (Configuración)
        left_panel = ttk.Frame(main_panel, width=300)
        self.build_configuration_panel(left_panel)
        main_panel.add(left_panel)

        # Panel derecho (Registro y previsualización)
        right_panel = ttk.Frame(main_panel)
        self.build_preview_panel(right_panel)
        main_panel.add(right_panel)

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

    def init_threads(self):
        """Inicializa los hilos para procesamiento en segundo plano."""
        # Hilo para procesar la cola de tareas (task_queue)
        self.task_thread = threading.Thread(
            target=self.process_queue,
            daemon=True,  # Se cerrará automáticamente al salir
        )
        self.task_thread.start()

        # Hilo para tareas programadas (schedule)
        self.schedule_thread = threading.Thread(
            target=self.run_scheduled_tasks, daemon=True
        )
        self.schedule_thread.start()

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
        self.log("Iniciando organización de archivos...")
        total_files = len(
            [
                f
                for f in os.listdir(directory)
                if os.path.isfile(os.path.join(directory, f))
            ]
        )
        processed = 0
        moved_files = []

        for filename in os.listdir(directory):
            src_path = os.path.join(directory, filename)
            if os.path.isfile(src_path):
                ext = os.path.splitext(filename)[1].lower()
                folder = self.profiles[self.current_profile]["formatos"].get(
                    ext, "Otros"
                )
                dest_dir = os.path.join(directory, folder)

                if not os.path.exists(dest_dir):
                    os.makedirs(dest_dir)

                dest_path = os.path.join(dest_dir, filename)
                try:
                    shutil.move(src_path, dest_path)
                    moved_files.append((src_path, dest_path))
                    self.log(f"Movido: {filename} -> {folder}")
                except Exception as e:
                    self.log(f"Error: {str(e)}")

                processed += 1
                self.update_progress(processed / total_files * 100)

        self.undo_stack.append(moved_files)
        self.log("Organización completada")
        self.update_progress(0)
        self.task_queue.put(self.show_stats(moved_files))

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

    def log(self, message):
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.log_area.insert(END, f"[{timestamp}] {message}\n")
        self.log_area.see(END)

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
        self.running = False

        # Espera un máximo de 1 segundo a que los hilos terminen
        if hasattr(self, "task_thread"):
            self.task_thread.join(timeout=1)
        if hasattr(self, "schedule_thread"):
            self.schedule_thread.join(timeout=1)

        self.save_to_file()
        self.destroy()


if __name__ == "__main__":
    app = FileOrganizerGUI()
    app.protocol("WM_DELETE_WINDOW", app.on_closing)
    app.mainloop()
