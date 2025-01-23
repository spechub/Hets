import logging
import os.path
import threading
from typing import Optional

import gi
import sys
from gi.repository.GLib import KeyFileFlags

from .ApplicationSettings import ApplicationSettings
from .utils import get_variant

gi.require_version("Gtk", "3.0")
from gi.repository import GLib, Gtk, Gio


class HetsApplication(Gtk.Application):
    """
    The main application class for the Hets GUI.
    """

    _logger = logging.getLogger(__name__)

    _reopen_libraries_menu_section: Optional[Gio.Menu]
    """ Menu section for opening already loaded libraries. """

    _refinement_trees_menu_section: Optional[Gio.Menu]
    """ Menu section for opening refinement trees. """

    _window: Optional[Gtk.Window]
    """ Start up window to be shown on application start. """

    _file: Optional[str]
    """ File to be opened on application start. """

    settings: ApplicationSettings
    """ Application specific settings. """


    def __init__(self):
        super().__init__(
            application_id="eu.hets.gui",
            flags=Gio.ApplicationFlags.HANDLES_OPEN)
        self._library_manager = None
        self._refinement_trees_menu_section = None
        self._reopen_libraries_menu_section = None

        self._window = None
        self._file = None

        # Set the application name
        GLib.set_application_name("Hets")

        # Declare that the application takes a file as an argument
        self.set_option_context_parameter_string("FILE")

        self.connect("open", self._on_open)

        # Load and register resources
        pgk_dir = os.path.dirname(os.path.realpath(__file__))
        resource_file = os.path.join(pgk_dir, "hetsgui.gresource")
        self._logger.debug("Loading resources from %s", resource_file)
        resource: Gio.Resource = Gio.resource_load(resource_file)
        Gio.resources_register(resource)

        # Add command line options
        self.add_main_option("log", ord('l'), GLib.OptionFlags.NONE, GLib.OptionArg.STRING, "Log level",
                             "<debug|info|warning|error>")
        self.connect("handle-local-options", self._on_handle_local_options)

        # Add actions on application level
        # Action to open a window for a library
        action_show_library = Gio.SimpleAction.new("open_win_for_lib", GLib.VariantType("s"))
        action_show_library.connect("activate", self._on_open_win_for_lib)
        self.add_action(action_show_library)

        # Action to show a window for a refinement tree
        action_show_refinement_tree = Gio.SimpleAction.new("open_refinement_tree", GLib.VariantType("av"))
        action_show_refinement_tree.connect("activate", self._on_open_refinement_tree)
        self.add_action(action_show_refinement_tree)

        # Load settings and add action to save settings to persist restarts
        self.load_settings()
        action_save_settings = Gio.SimpleAction.new("save_settings", None)
        action_save_settings.connect("activate", lambda _1, _2: self.save_settings())
        self.add_action(action_save_settings)

    def load_settings(self):
        """
        Load the application settings from the users config directory if existing.
        :return:
        """

        path = os.path.join(GLib.get_user_config_dir(), "hets", "settings.ini")
        file = GLib.KeyFile()
        self.settings = ApplicationSettings(file)

        if os.path.exists(path):
            file.load_from_file(path, KeyFileFlags.NONE)

    def save_settings(self):
        """
        Save the application settings to the users config directory.
        :return:
        """
        self._logger.debug("Saving settings")
        dir = os.path.join(os.path.join(GLib.get_user_config_dir(), "hets"))

        os.makedirs(dir, exist_ok=True)

        path = os.path.join(dir, "settings.ini")
        self.settings.keyfile.save_to_file(path)

    def _on_open_win_for_lib(self, action: Gio.SimpleAction, parameter: GLib.Variant):
        """
        Handler for the open_win_for_lib action.

        Opens a window for the given library.
        :param action: ignored
        :param parameter: name of or path to the library to open
        :return:
        """

        if self._library_manager is not None:
            self._library_manager.show_library(parameter.get_string())

    def _on_open_refinement_tree(self, action: Gio.SimpleAction, parameter: GLib.Variant):
        """
        Handler for the open_refinement_tree action.

        Opens a window for the given refinement tree.

        :param action: ignored
        :param parameter: tuple of library id and library name
        :return:
        """


        if self._library_manager is not None:
            library_id, spec_name = parameter.unpack()

            self._library_manager.show_refinement_tree(library_id, spec_name)

    def _on_handle_local_options(self, application, options: GLib.VariantDict):
        """
        Handler for the handle-local-options signal.

        Sets up the logging based options provided from the command line.

        :param application: ignored
        :param options: options provided from the command line
        :return:
        """

        log_value = options.lookup_value("log")
        log_level_int = logging.DEBUG
        if log_value is not None:
            log_level = log_value.get_string().upper()
            log_level_int = getattr(logging, log_level.upper(), None)
            if not isinstance(log_level_int, int):
                print('Invalid log level: %s' % log_level, file=sys.stderr)
                return 1

        logging.basicConfig(
            level=log_level_int,
            format='[%(asctime)s.%(msecs)03d] [ %(levelname)-7s ] [%(name)s] %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S',
        )

        return -1

    def do_startup(self):
        """
        Handler for the startup signal.

        Sets up the application and gets reference to UI variables
        :return:
        """

        Gtk.Application.do_startup(self)
        self._reopen_libraries_menu_section = self.get_menu_by_id("reopen-section")
        self._refinement_trees_menu_section = self.get_menu_by_id("refinement-trees")

    def do_command_line(self, command_line):
        self.activate()
        return 0

    def _on_open(self, action, files, n_files, hint):
        """
        Handler for the open signal.

        Opens the selected file.

        :param action: ignored
        :param files: selected files to open
        :param n_files: number of files to open (because C array)
        :param hint: ignored
        :return:
        """
        if n_files != 1:
            print("Expected exactly one file", file=sys.stderr)
            return 1

        self._file = files[0].get_path()
        self.do_activate()

    def do_activate(self):
        """
        Starts the application.

        Loads necessary libraries and shows a loading window in the meantime.

        :return:
        """

        if not self._window:
            # The loading window
            from .windows.StartUpWindow import StartUpWindow
            startup_window = StartUpWindow(application=self)
            startup_window.show_all()
            startup_window.present()

            self._window = startup_window

            def start_up_done():
                from .LibraryManager import LibraryManager
                from hets import Options

                self._library_manager = LibraryManager(self)
                self._library_manager.connect("new-library", self._on_new_library)
                self._library_manager.connect("new-refinement-tree-spec", self._on_new_refinement_tree_spec)

                startup_window.close()

                if self._file:
                    default_options = Options(libdirs=os.environ.get("HETS_LIB", []))
                    self._library_manager.load_file(self._file, default_options)
                else:
                    self._library_manager.show_default_window()

                self._window.show_all()
                self._window.present()
                # self.set_action_group()

            # noinspection PyUnresolvedReferences
            def start_up():
                self._logger.info("Loading python libraries")
                import hets
                self._logger.info("Loading python libraries done")

                # Changes to UI must be executed on the main thread / UI thread
                GLib.idle_add(start_up_done)

            # Load the libraries in the background
            t = threading.Thread(target=start_up)
            t.start()

        self._window.show_all()
        self._window.present()

    def _on_new_library(self, sender, library_id: str):
        """
        Handler for the new-library signal.

        Adds a menu item for the new library to the reopen libraries menu section.

        :param sender: ignored
        :param library_id: id of the new library
        :return:
        """

        if self._reopen_libraries_menu_section:
            item = Gio.MenuItem()
            item.set_label(library_id)
            item.set_action_and_target_value("app.open_win_for_lib", get_variant(library_id))

            self._reopen_libraries_menu_section.append_item(item)

    def _on_new_refinement_tree_spec(self, sender, library_id: str, spec_name: str):
        """
        Handler for the new-refinement-tree-spec signal.

        Adds a menu item for the new refinement tree to the refinement trees menu section.

        :param sender: ignored
        :param library_id: id of the library
        :param spec_name: name of the spec
        :return:
        """

        if self._refinement_trees_menu_section:
            item = Gio.MenuItem()
            item.set_label(f"{library_id}: {spec_name}")
            item.set_action_and_target_value("app.open_refinement_tree", get_variant((library_id, spec_name)))

            self._refinement_trees_menu_section.append_item(item)
