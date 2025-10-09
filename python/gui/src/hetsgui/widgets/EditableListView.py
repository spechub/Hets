import gi
from gi.repository import Gtk, GObject

from ..GtkSmartTemplate import GtkSmartTemplate


@GtkSmartTemplate
class EditableListView(Gtk.Bin):
    """
    A list view that allows to add and delete rows as well as editing the content of the cells.
    """

    __gtype_name__ = "EditableListView"

    model = GObject.Property(type=Gtk.ListStore)

    _btn_delete: Gtk.Button = Gtk.Template.Child()
    _treeview: Gtk.TreeView = Gtk.Template.Child()

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        self.connect("notify::model", self._on_model_changed)

        self.model = Gtk.ListStore(str)

    @Gtk.Template.Callback()
    def on_add_button_clicked(self, *args):
        # Add empty row
        self.model.append([""] * self.model.get_n_columns())

    @Gtk.Template.Callback()
    def on_delete_button_clicked(self, *args):
        # Get the selected row and remove it
        model, selected = self._treeview.get_selection().get_selected()

        model.remove(selected)

    @Gtk.Template.Callback()
    def on_treeview_selection_changed(self, *args):
        # Enable delete button iif a row is selected
        model, selected = self._treeview.get_selection().get_selected()

        self._btn_delete.set_sensitive(selected)

    @Gtk.Template.Callback()
    def on_text_edited(self, widget, path, text: str, index: int):
        self.model[path][index] = text

    def _on_model_changed(self, *args):
        # Remove all columns from a potential previous model
        columns = self._treeview.get_columns()
        for column in columns:
            self._treeview.remove_column(column)

        # Add a column for each column in the model
        num_columns = self.model.get_n_columns()
        for i in range(num_columns):
            renderer = Gtk.CellRendererText(editable=True, placeholder_text="Type here...")
            renderer.connect("edited", self.on_text_edited, i)
            column = Gtk.TreeViewColumn("", renderer, text=i)
            self._treeview.append_column(column)

        self._treeview.set_model(self.model)
