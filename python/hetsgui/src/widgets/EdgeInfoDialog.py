from gi.repository import Gtk

from hets import DevGraphEdge


class EdgeInfoDialog(Gtk.Dialog):
    def __init__(self, parent, edge: DevGraphEdge):
        super().__init__(transient_for=parent, flags=0)

        self.set_default_size(800, 600)
        self.add_buttons("_Close", Gtk.ResponseType.CLOSE)

        title = f"edge {edge.id()} {edge.name()}({edge.origin()} --> {edge.target()})"
        self.set_title(title)

        box = self.get_content_area()
        text_view = Gtk.TextView()
        text_view.set_property('editable', False)
        text_view.set_property('monospace', True)
        text_buffer = text_view.get_buffer()
        text_buffer.set_text(title + "\n" + edge.info())

        box.add(text_view)
        self.show_all()
