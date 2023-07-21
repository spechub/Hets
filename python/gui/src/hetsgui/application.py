#!/usr/bin/env python3

import os.path
import sys
import threading
import logging

import gi

gi.require_version("Gtk", "3.0")
from gi.repository import GLib, Gtk, Gio


class HetsApplication(Gtk.Application):
    logger = logging.getLogger(__name__)

    def __init__(self):
        super().__init__(
            application_id="eu.hets.gui",
            flags=Gio.ApplicationFlags.HANDLES_OPEN)
        GLib.set_application_name("Hets")
        self.set_option_context_parameter_string("FILE")

        self.connect("open", self.on_open)

        self.window = None
        self.file = None

        pgk_dir = os.path.dirname(os.path.realpath(__file__))
        resource_file = os.path.join(pgk_dir, "hetsgui.gresource")
        self.logger.debug("Loading resources from %s", resource_file)
        resource: Gio.Resource = Gio.resource_load(resource_file)
        Gio.resources_register(resource)

        self.add_main_option("log", ord('l'), GLib.OptionFlags.NONE, GLib.OptionArg.STRING, "Log level", "<debug|info|warning|error>")
        self.connect("handle-local-options", self.on_handle_local_options)

    def on_handle_local_options(self, application, options: GLib.VariantDict):
        log_value = options.lookup_value("log")
        if log_value is not None:
            log_level = log_value.get_string().upper()
            log_level_int = getattr(logging, log_level.upper(), None)
            if not isinstance(log_level_int, int):
                print('Invalid log level: %s' % log_level, file=sys.stderr)
                return 1
            logging.basicConfig(level=log_level_int)

        return -1

    def do_startup(self):
        Gtk.Application.do_startup(self)
        builder = Gtk.Builder.new_from_resource("/eu/hets/hetsgui/resources/application-menu.xml")
        menubar = builder.get_object("app-menu")

        self.set_menubar(menubar)

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
                from .windows.MainWindow import MainWindow

                self.window = MainWindow(application=self)
                startup_window.close()

                if self.file:
                    self.window.open_file(self.file)

                self.window.show_all()
                self.window.present()

            # noinspection PyUnresolvedReferences
            def start_up():
                self.logger.info("Loading python libraries")
                import hets
                self.logger.info("Loading python libraries done")

                GLib.idle_add(start_up_done)

            t = threading.Thread(target=start_up)
            t.start()

        self.window.show_all()
        self.window.present()
