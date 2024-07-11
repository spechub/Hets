import os.path
import sys
import threading
import logging
import typing
from typing import Optional

import gi

from hetsgui.utils import get_variant

gi.require_version("Gtk", "3.0")
from gi.repository import GLib, Gtk, Gio


class HetsApplication(Gtk.Application):
    _logger = logging.getLogger(__name__)

    _reopen_libraries_menu_section: Optional[Gio.Menu]
    _refinement_trees_menu_section: Optional[Gio.Menu]

    def __init__(self):
        super().__init__(
            application_id="eu.hets.gui",
            flags=Gio.ApplicationFlags.HANDLES_OPEN)
        self._library_manager = None
        self._refinement_trees_menu_section = None
        self._reopen_libraries_menu_section = None
        GLib.set_application_name("Hets")
        self.set_option_context_parameter_string("FILE")

        self.connect("open", self.on_open)

        self.window = None
        self.file = None

        pgk_dir = os.path.dirname(os.path.realpath(__file__))
        resource_file = os.path.join(pgk_dir, "hetsgui.gresource")
        self._logger.debug("Loading resources from %s", resource_file)
        resource: Gio.Resource = Gio.resource_load(resource_file)
        Gio.resources_register(resource)

        self.add_main_option("log", ord('l'), GLib.OptionFlags.NONE, GLib.OptionArg.STRING, "Log level",
                             "<debug|info|warning|error>")
        self.connect("handle-local-options", self._on_handle_local_options)

        action_show_library = Gio.SimpleAction.new("open_win_for_lib", GLib.VariantType("s"))
        action_show_library.connect("activate", self._on_open_win_for_lib)
        self.add_action(action_show_library)

        action_show_refinement_tree = Gio.SimpleAction.new("open_refinement_tree", GLib.VariantType("av"))
        action_show_refinement_tree.connect("activate", self._on_open_refinement_tree)
        self.add_action(action_show_refinement_tree)

    def _on_open_win_for_lib(self, action: Gio.SimpleAction, parameter: GLib.Variant):
        if self._library_manager is not None:
            self._library_manager.show_library(parameter.get_string())

    def _on_open_refinement_tree(self, action: Gio.SimpleAction, parameter: GLib.Variant):
        if self._library_manager is not None:
            library_id, spec_name = parameter.unpack()

            self._library_manager.show_refinement_tree(library_id, spec_name)

    def _on_handle_local_options(self, application, options: GLib.VariantDict):
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
        Gtk.Application.do_startup(self)
        self._reopen_libraries_menu_section = self.get_menu_by_id("reopen-section")
        self._refinement_trees_menu_section = self.get_menu_by_id("refinement-trees")

    def do_command_line(self, command_line):
        self.activate()
        return 0

    def on_open(self, a, files, n_files, hint):
        if n_files != 1:
            print("Expected exactly one file", file=sys.stderr)
            return 1

        self.file = files[0].get_path()
        self.do_activate()

    def do_activate(self):
        if not self.window:
            from .windows.StartUpWindow import StartUpWindow
            startup_window = StartUpWindow(application=self)
            startup_window.show_all()
            startup_window.present()

            self.window = startup_window

            def start_up_done():
                from .LibraryManager import LibraryManager
                from hets import Options

                self._library_manager = LibraryManager(self)
                self._library_manager.connect("new-library", self._on_new_library)
                self._library_manager.connect("new-refinement-tree-spec", self._on_new_refinement_tree_spec)

                startup_window.close()

                if self.file:
                    default_options = Options(libdirs=[os.environ["HETS_LIB"]] if "HETS_LIB" in os.environ else [])
                    self._library_manager.load_file(self.file, default_options)
                else:
                    self._library_manager.show_default_window()

                self.window.show_all()
                self.window.present()
                # self.set_action_group()

            # noinspection PyUnresolvedReferences
            def start_up():
                self._logger.info("Loading python libraries")
                import hets
                self._logger.info("Loading python libraries done")

                GLib.idle_add(start_up_done)

            t = threading.Thread(target=start_up)
            t.start()

        self.window.show_all()
        self.window.present()

    def _on_new_library(self, sender, library_id: str):
        if self._reopen_libraries_menu_section:
            item = Gio.MenuItem()
            item.set_label(library_id)
            item.set_action_and_target_value("app.open_win_for_lib", get_variant(library_id))

            self._reopen_libraries_menu_section.append_item(item)

    def _on_new_refinement_tree_spec(self, sender, library_id: str, spec_name: str):
        if self._refinement_trees_menu_section:
            item = Gio.MenuItem()
            item.set_label(f"{library_id}: {spec_name}")
            item.set_action_and_target_value("app.open_refinement_tree", get_variant((library_id, spec_name)))

            self._refinement_trees_menu_section.append_item(item)


