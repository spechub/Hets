import gi
from gi.repository import Gtk, GObject

from actions.model import toggle_tree_view_cell_handler, toggle_tree_view_header_cell_handler


class SelectableTreeView(Gtk.TreeView):
    __gtype_name__ = "SelectableTreeView"

    @GObject.Property(type=int, default=0)
    def selected_column(self) -> int:
        return self._selected_column

    @selected_column.setter
    def selected_column(self, cid: int):
        self._selected_column = cid
        self._column.add_attribute(self._cell_renderer, "active", cid)

    def __init__(self, **kwargs):
        Gtk.TreeView.__init__(self)

        self._selected_column = 0

        self._column = Gtk.TreeViewColumn()
        self._column.set_clickable(True)

        self._cell_renderer = Gtk.CellRendererToggle()
        self._cell_renderer.connect_object("toggled", toggle_tree_view_cell_handler, self._column)
        self._column.pack_start(self._cell_renderer, False)

        self._header_switch = Gtk.CheckButton(active=True)
        self._header_switch.show_all()
        self._column.set_widget(self._header_switch)
        self._column.connect("clicked", toggle_tree_view_header_cell_handler)

        self.insert_column(self._column, 0)
