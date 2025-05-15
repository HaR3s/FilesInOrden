import tkinter as tk
from tkinter import ttk
from PIL import Image, ImageTk
import os


def mostrar_iconos():
    root = tk.Tk()
    root.title("Debug de Iconos")

    # Mapeo de iconos (debe coincidir con tu estructura de directorios)
    icon_mapping = {
        "file": "document.png",
        "folder": "folder.png",
        "image": "image.png",
        "PDFs": "pdf.png",
        "video": "video.png",
        "audio": "audio.png",
        "archive": "archive.png",
        "error": "error.png",
    }

    # Frame para contener los iconos
    frame = ttk.Frame(root, padding=10)
    frame.pack()

    # Verificar si existe el directorio "icons"
    if not os.path.exists("icons"):
        tk.Label(frame, text="❌ No existe el directorio 'icons'").pack()
        return

    # Cargar y mostrar cada ícono
    for icon_name, filename in icon_mapping.items():
        icon_path = os.path.join("icons", filename)

        if not os.path.exists(icon_path):
            tk.Label(frame, text=f"❌ {filename} no existe").pack()
            continue

        try:
            img = Image.open(icon_path)
            img = img.resize(
                (32, 32), Image.Resampling.LANCZOS
            )  # Redimensionar para mejor visualización
            photo_img = ImageTk.PhotoImage(img)

            # Mostrar el ícono y su nombre
            icon_frame = ttk.Frame(frame)
            icon_frame.pack(pady=5, fill=tk.X)

            label_img = ttk.Label(icon_frame, image=photo_img)
            label_img.image = photo_img  # ¡Mantener referencia!
            label_img.pack(side=tk.LEFT)

            ttk.Label(icon_frame, text=f"{icon_name} ({filename})").pack(
                side=tk.LEFT, padx=10
            )
        except Exception as e:
            ttk.Label(frame, text=f"❌ Error cargando {filename}: {str(e)}").pack()

    root.mainloop()


if __name__ == "__main__":
    mostrar_iconos()
