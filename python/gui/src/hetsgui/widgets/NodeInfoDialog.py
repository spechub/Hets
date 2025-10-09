from gi.repository import Gtk

from hets import DevGraphNode


class NodeInfoDialog(Gtk.Dialog):
    """
    Dialog to show information about a DevGraphNode.
    """
    def __init__(self, node: DevGraphNode):
        super().__init__()

        self.set_default_size(800, 600)

        title = "{0}node {1} {2}".format(
            ("reference " if node.is_reference_node() else "internal " if node.is_internal() else ""),
            node.name(),
            node.id())
        self.set_title(title)

        box = self.get_content_area()
        scrolled_window = Gtk.ScrolledWindow(expand=True)

        text_view = Gtk.TextView()
        text_view.set_property('editable', False)
        text_view.set_property('monospace', True)
        text_buffer = text_view.get_buffer()
        text_buffer.set_text(title + "\n" + node.info())

        scrolled_window.add(text_view)
        box.add(scrolled_window)
        self.show_all()
