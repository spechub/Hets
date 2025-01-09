from gi.repository import Gtk

from hets import DevGraphNode


class TheoryInfoDialog(Gtk.Dialog):
    def __init__(self, node: DevGraphNode):
        super().__init__()

        self.set_default_size(800, 600)

        title = "Theory of {0}node {1} {2}".format(
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
        text_buffer.set_text(str(node.theory()))

        # button = Gtk.Button(label="Save")
        # button.connect("clicked", self._on_save)

        scrolled_window.add(text_view)
        box.add(scrolled_window)
        # box.add(button)
        self.show_all()

    # def _on_save(self, widget: Gtk.Widget, target: None):
    #     Gtk.FileChooserDialog()
