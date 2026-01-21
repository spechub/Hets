import os.path

from gi.repository import Gtk

from ..GtkSmartTemplate import GtkSmartTemplate


@GtkSmartTemplate
class StartUpWindow(Gtk.Window):
    __gtype_name__ = "StartUpWindow"

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        icon = os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../resources/icon.png"))
        self.set_default_icon_from_file(icon)

        self.show_all()
