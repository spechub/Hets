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
            print(self.file)
            self.window = MainWindow(self.file, application=self)

        self.window.show_all()
        self.window.present()

app = MyApplication()
exit_status = app.run(sys.argv)
sys.exit(exit_status)
