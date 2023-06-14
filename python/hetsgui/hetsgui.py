import sys

import gi

gi.require_version("Gtk", "3.0")
from gi.repository import GLib, Gtk, Gio

class MyApplication(Gtk.Application):
    def __init__(self):
        super().__init__(
            application_id="eu.hets.hets",
            flags=Gio.ApplicationFlags.HANDLES_OPEN)
        GLib.set_application_name("Hets")
        self.set_option_context_parameter_string("FILE")

        self.connect("open", self.on_open)

        self.window = None
        self.file = None

    def _set_menu(self):
        file_menu = Gio.Menu()

        menu_entry_open = Gio.MenuItem()
        menu_entry_open.set_label("Open")
        menu_entry_open.set_action_and_target_value("win.open_file", None)
        file_menu.append_item(menu_entry_open)

        menu = Gio.Menu()
        menu.append_submenu("File", file_menu)
        self.set_menubar(menu)

    def do_startup(self):
        Gtk.Application.do_startup(self)
        self._set_menu()

    def on_action_open_file(self, action, parameter):
        print("Hello World!")

    def do_command_line(self, command_line):
        options = command_line.get_options_dict()
        # convert GVariantDict -> GVariant -> dict
        options = options.end().unpack()

        self.activate()
        return 0

    def on_open(self, a, files, n_files, hint):
        if n_files != 1:
            print("Expected exactly one file")
            return 1

        self.file = files[0].get_path()
        self.do_activate()

    def do_activate(self):
        if not self.window:
            from windows.MainWindow import MainWindow
            self.window = MainWindow(application=self)

            if self.file:
                self.window.open_file(self.file)

        print(self.get_app_menu())
        self.window.show_all()
        self.window.present()

app = MyApplication()
exit_status = app.run(sys.argv)
sys.exit(exit_status)
