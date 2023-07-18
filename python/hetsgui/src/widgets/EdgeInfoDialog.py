from gi.repository import Gtk

from hets import DevGraphEdge


class EdgeInfoDialog(Gtk.Dialog):
    def __init__(self, edge: DevGraphEdge):
        super().__init__()

        self.set_default_size(800, 600)

        title = f"edge {edge.id()} {edge.name()}({edge.origin()} --> {edge.target()})"
        self.set_title(title)

        box = self.get_content_area()
        scrolled_window = Gtk.ScrolledWindow(expand=True)

        text_view = Gtk.TextView()
        text_view.set_property('editable', False)
        text_view.set_property('monospace', True)
        text_buffer = text_view.get_buffer()
        text_buffer.set_text(title + "\n" + edge.info())

        scrolled_window.add(text_view)
        box.add(scrolled_window)
        self.show_all()
