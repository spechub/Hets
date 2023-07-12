import gi
from gi.repository import Gtk, GObject

from xdot import DotWidget


class ExtendedDotWidget(DotWidget):
    __gtype_name__ = "ExtendedDotWidget"

    dotcode = GObject.Property(type=str)

    def __init__(self):
        super().__init__()

        self.connect("notify::dotcode", self.on_dotcode_changed)

    def on_dotcode_changed(self, widget, param):
        dotcode = self.dotcode.encode("utf8")

        self.set_dotcode(dotcode)
