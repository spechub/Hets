import logging
import os.path
import typing
from typing import Dict, Optional

from gi.repository import Gtk, Gio, GObject

from hets import Library, load_library, Options
from .windows.LibraryWindow import LibraryWindow
from .windows.MainWindow import MainWindow
from .windows.RefinementTreeWindow import RefinementTreeWindow


class LibraryManager(GObject.GObject):
    """
    Class to manage the loaded libraries and windows.
    """

    # Register signals
    __gsignals__ = {
        # Signal emitted when a new library is loaded
        "new-library": (GObject.SIGNAL_RUN_FIRST, None, (str,)),

        # Signal emitted when a new refinement tree specification is loaded
        "new-refinement-tree-spec": (GObject.SIGNAL_RUN_FIRST, None, (str, str))
    }

    _logger = logging.getLogger(__name__)

    _loaded_library_paths: Dict[str, str]
    """ Mapping of loaded library paths to library ids. """

    _loaded_libraries: Dict[str, Library]
    """ Mapping of ids of to loaded libraries. """

    _open_windows: Dict[str, MainWindow]
    """ Mapping of library ids to their window. """

    _open_refinement_tree_windows: Dict[str, RefinementTreeWindow]
    """ Mapping of library ids and spec names to their refinement tree window. """

    _default_window: Optional[MainWindow]
    """ Default window to be used when no other window is open. """

    _library_graph_window: Optional[LibraryWindow]
    """ Window showing the library graph. """

    def __init__(self, application: Gio.Application):
        super().__init__()
        self._library_graph_window = None
        self._loaded_libraries = {}
        self._known_libnames = {}
        self._open_windows = {}
        self._open_refinement_tree_windows = {}
        self._loaded_library_paths = {}
        self._default_window = None

        self._application = application

    def _new_window(self) -> MainWindow:
        """
        Helper function to create a new main window connecting its signals to this instance.
        :return: Initialized main window instance.
        """

        window = MainWindow(application=self._application)
        window.connect("load-file", self.on_load_file)
        window.connect("show-library", self.on_show_library)
        window.connect("show-library-graph", self.on_show_library_graph)
        window.connect("destroy", self._on_window_destroyed)

        return window

    def _on_window_destroyed(self, window: MainWindow):
        """
        Handler for the destroy signal of a window.

        Removes the window from the list of open windows.

        :param window: The destroyed window.
        :return:
        """

        key = next((k for k, v in self._open_windows.items() if v == window), None)

        if key is None:
            self._logger.warning(
                "Trying to clean up a destroyed window but the window was not found in the list of open windows")
        else:
            del self._open_windows[key]

    def show_default_window(self):
        """
        Shows the default window.

        If no default window is set, a new one is created.
        :return:
        """

        if self._default_window is None:
            self._default_window = self._new_window()
            
        self._default_window.show_all()
        self._default_window.present()

    def on_show_library(self, sender, library_id: str):
        """
        Handler for the show-library signal from library windows.

        :param sender: ignored
        :param library_id: id of the library to show
        :return:
        """

        self.show_library(library_id)

    def on_load_file(self, sender, file: str, settings: Options):
        """
        Handler for the load-file signal from library windows.

        :param sender: ignored
        :param file: File to load
        :param settings: HetsCats object with library settings
        :return:
        """

        self.load_file(file, settings)

    def load_file(self, file: str, settings: Options):
        """
        Load a library from a file.

        :param file: File to load
        :param settings: HetsCats object with library settings
        :return:
        """

        file = os.path.abspath(file)

        # Only load the library if it is not already loaded
        if file in self._loaded_library_paths:
            self.show_library(self._loaded_library_paths[file])
            return

        try:
            # Load and register the library, referenced libraries, and refinement tree specifications
            library = load_library(file, settings)
            library_id = library.name().id()
            for name, _ in library.environment():
                self._loaded_libraries[name.id()] = Library((name._hs_libname, library._env))

                self.emit("new-library", name.id())

            self._loaded_library_paths[file] = library_id

            for spec in self._loaded_libraries[library_id].specifications():
                self.emit("new-refinement-tree-spec", library_id, spec)

            self.show_library(library_id)
        except Exception as e:
            # Unfortunately, we cannot capture the output from the console here

            self._logger.error(f"Failed to load file '{file}': %s", e)

            dialog = Gtk.MessageDialog(flags=0, message_type=Gtk.MessageType.ERROR,
                                       buttons=Gtk.ButtonsType.CLOSE, text=f"Failed to load {file}!")
            dialog.format_secondary_text(f"Check the console for more details.\nError message: {str(e)}")
            dialog.run()
            dialog.destroy()
            return

    def show_library(self, library_id: str):
        """
        Show the loaded library with the given id.

        Does nothing if a library with the ID is not loaded

        :param library_id: id of the loaded library to show
        :return:
        """

        if library_id not in self._open_windows:
            # Reuse the default window if no other library used it before
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
        """
        Show the library graph of a loaded library with the given id.

        :param library_id: Id of the loaded library.
        :return:
        """
        if library_id not in self._loaded_libraries:
            self._logger.error(f"Tried to open library graph for an unloaded library with id {library_id}!")

        # Show only one library graph window at a time
        if self._library_graph_window is None:
            self._library_graph_window = LibraryWindow(self._loaded_libraries[library_id],
                                                       application=self._application)

            def on_destroy(_):
                self._library_graph_window = None

            self._library_graph_window.connect("destroy", on_destroy)

        self._library_graph_window.show_all()
        self._library_graph_window.present()

    def on_show_refinement_tree(self, sender, library_and_spec: typing.Tuple[str, str]):
        library_id, spec_name = library_and_spec
        self.show_refinement_tree(library_id, spec_name)

    def show_refinement_tree(self, library_id: str, spec_name: str):
        """
        Show the refinement tree for a loaded library with the given id and spec name.

        :param library_id: ID of the loaded library
        :param spec_name: Name of the spec
        :return:
        """

        if library_id not in self._loaded_libraries:
            self._logger.error(
                f"Tried to open refinement tree for spec '{spec_name}' of an unloaded library with id {library_id}!")

        spec_id = f"{library_id}/{spec_name}"
        if spec_id not in self._open_refinement_tree_windows:
            self._open_refinement_tree_windows[spec_id] = RefinementTreeWindow(self._loaded_libraries[library_id],
                                                                               spec_name,
                                                                               application=self._application)

            def on_destroy(_):
                del self._open_refinement_tree_windows[spec_id]

            self._open_refinement_tree_windows[spec_id].connect("destroy", on_destroy)

        self._open_refinement_tree_windows[spec_id].show_all()
        self._open_refinement_tree_windows[spec_id].present()
