import gi
from gi.repository import Gio, GLib, Gtk


def toggle_tree_view_header_cell_handler(column: Gtk.TreeViewColumn, index=1):
    tree_view: Gtk.TreeView = column.get_tree_view()
    model = tree_view.get_model()
    widget = column.get_widget()

    if not isinstance(widget, Gtk.CheckButton):
        return

    new_state = not (widget.get_inconsistent() or widget.get_active())

    for row in model:
        row[index] = new_state

    widget.set_inconsistent(False)
    widget.set_active(new_state)


def toggle_tree_view_cell_handler(toggle_column: Gtk.TreeViewColumn, path: str, index=1):
    tree_view: Gtk.TreeView = toggle_column.get_tree_view()
    model = tree_view.get_model()

    header = toggle_column.get_widget()

    next_state = not model[path][index]

    model[path][index] = next_state

    if header is not None and isinstance(header, Gtk.CheckButton):
        consistent = all(row[index] == next_state for row in model)
        header.set_inconsistent(not consistent)
        header.set_active(next_state)
