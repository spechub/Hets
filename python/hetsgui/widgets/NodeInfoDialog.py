from gi.repository import Gtk

from hets import DevGraphNode


class NodeInfoDialog(Gtk.Dialog):
    def __init__(self, parent, node: DevGraphNode):
        super().__init__(transient_for=parent, flags=0)

        self.set_default_size(800, 600)
        self.add_buttons("_Close", Gtk.ResponseType.CLOSE)

        title = "{0} node {1} {2}".format(
            ("reference" if node.is_reference_node() else "internal" if node.is_internal() else ""),
            node.name(),
            node.id())
        self.set_title(title)

        box = self.get_content_area()
        text_view = Gtk.TextView()
        text_view.set_property('editable', False)
        text_buffer = text_view.get_buffer()
        text_buffer.set_text(title + "\n" + node.info())

        box.add(text_view)
        self.show_all()
