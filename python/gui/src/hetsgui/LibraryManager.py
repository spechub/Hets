import logging
import os.path
from typing import Dict, Optional

from gi.repository import Gtk, Gio, GObject

from hets import Library, load_library, Options
from .windows.LibraryWindow import LibraryWindow
from .windows.MainWindow import MainWindow


class LibraryManager(GObject.GObject):
    __gsignals__ = {
        "new-library": (GObject.SIGNAL_RUN_FIRST, None, (str,))
    }

    _logger = logging.getLogger(__name__)

    _loaded_library_paths: Dict[str, str]
    _loaded_libraries: Dict[str, Library]
    _open_windows: Dict[str, MainWindow]

    _default_window: Optional[MainWindow]
    _library_graph_window: Optional[LibraryWindow]

    def __init__(self, application: Gio.Application):
        super().__init__()
        self._library_graph_window = None
        self._loaded_libraries = {}
        self._known_libnames = {}
        self._open_windows = {}
        self._loaded_library_paths = {}
        self._default_window = None

        self._application = application

    def _new_window(self) -> MainWindow:
        window = MainWindow(application=self._application)
        window.connect("load-file", self.on_load_file)
        window.connect("show-library", self.on_show_library)
        window.connect("show-library-graph", self.on_show_library_graph)
        window.connect("destroy", self._on_window_destroyed)

        return window

    def _on_window_destroyed(self, window: MainWindow):
        key = next((k for k, v in self._open_windows.items() if v == window), None)

        if key is None:
            self._logger.warning(
                "Trying to clean up a destroyed window but the window was not found in the list of open windows")
        else:
            del self._open_windows[key]

    def show_default_window(self):
        if self._default_window is None:
            self._default_window = self._new_window()

    def on_show_library(self, sender, library_id: str):
        self.show_library(library_id)

    def on_load_file(self, sender, file: str, settings: Options):
        self.load_file(file, settings)

    def load_file(self, file: str, settings: Options):
        file = os.path.abspath(file)

        if file in self._loaded_library_paths:
            self.show_library(self._loaded_library_paths[file])
            return

        try:
            library = load_library(file, settings)
            library_id = library.name().id()
            # self._loaded_libraries[library_id] = library
            for name, _ in library.environment():
                self._loaded_libraries[name.id()] = Library((name._hs_libname, library._env))

                self.emit("new-library", name.id())

            self._loaded_library_paths[file] = library_id

            self.show_library(library_id)
        except Exception as e:
            # self._set_library_actions_enabled(False)
            self._logger.error(f"Failed to load file '{file}': %s", e)

            dialog = Gtk.MessageDialog(transient_for=self, flags=0, message_type=Gtk.MessageType.ERROR,
                                       buttons=Gtk.ButtonsType.CLOSE, text=f"Failed to load {file}!")
            dialog.format_secondary_text(f"Check the console for more details.\nError message: {str(e)}")
            dialog.run()
            dialog.destroy()
            return

    def show_library(self, library_id: str):
        if library_id not in self._open_windows:
            if self._default_window is not None:
                window = self._default_window
                self._default_window = None
            else:
                window = self._new_window()

            window.use_library(self._loaded_libraries[library_id])

            self._open_windows[library_id] = window

        self._open_windows[library_id].show_all()
        self._open_windows[library_id].present()

    def on_show_library_graph(self, sender, library_id: str):
        self.show_library_graph(library_id)

    def show_library_graph(self, library_id: str):
        if library_id not in self._loaded_libraries:
            self._logger.error(f"Tried to open library graph for an unloaded library with id {library_id}!")

        if self._library_graph_window is None:
            self._library_graph_window = LibraryWindow(self._loaded_libraries[library_id],
                                                       application=self._application)

            def on_destroy(_):
                self._library_graph_window = None

            self._library_graph_window.connect("destroy", on_destroy)

        self._library_graph_window.show_all()
        self._library_graph_window.present()
