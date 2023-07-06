import cairo
from gi.repository import Gtk, GObject, Gdk


class CellRendererLink(Gtk.CellRendererText):
    __gsignals__ = {"clicked": (GObject.SIGNAL_RUN_FIRST, None, (str,))}

    def __init__(self, **kwargs):
        super().__init__()
        self.set_property("mode", Gtk.CellRendererMode.ACTIVATABLE)

        self.button = Gtk.Button()

    def do_activate(self, event, widget, path, background_area, cell_area, flags):
        self.emit('clicked', path)
