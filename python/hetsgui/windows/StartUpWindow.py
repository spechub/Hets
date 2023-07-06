import os.path

from gi.repository import Gtk, Gdk


class StartUpWindow(Gtk.Window):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        icon = os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../hets.png"))
        self.set_default_icon_from_file(icon)

        self.set_decorated(False)
        self.set_position(Gtk.WindowPosition.CENTER_ALWAYS)
        self.set_resizable(False)
        self.set_auto_startup_notification(False)
        # self.set_skip_taskbar_hint(True)
        self.set_skip_pager_hint(True)

        print(self.class_path())
        provider = Gtk.CssProvider()
        provider.load_from_data(b"""
        window {
            background-color: blue;
            background: linear-gradient(45deg, rgba(9,9,121,1) 0%, rgba(0,212,255,1) 100%);
            color: white;  
        }
        """)
        self.get_style_context().add_provider(provider, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)

        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, margin=14)
        title = Gtk.Label()
        title.set_markup('<span size="x-large">Hets - Heterogeneous Tool Set</span>')
        spinner = Gtk.Spinner(active=True)
        info = Gtk.Label(label="Loading libraries ...")

        box.pack_start(title, True, False, 14)
        box.pack_start(spinner, True, False, 4)
        box.pack_start(info, True, False, 4)

        self.add(box)
        self.show_all()
