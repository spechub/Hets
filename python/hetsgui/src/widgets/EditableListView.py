import gi
from gi.repository import Gtk, GObject

from GtkSmartTemplate import GtkSmartTemplate


@GtkSmartTemplate
class EditableListView(Gtk.Bin):
    __gtype_name__ = "EditableListView"

    model = GObject.Property(type=Gtk.ListStore, default=Gtk.ListStore(str))

    _btn_delete: Gtk.Button = Gtk.Template.Child()
    _treeview: Gtk.TreeView = Gtk.Template.Child()

    def __init__(self):
        super().__init__()

        self._treeview.set_model(self.model)
        self.bind_property("model", self._treeview, "model", GObject.BindingFlags.BIDIRECTIONAL)



    @Gtk.Template.Callback()
    def on_add_button_clicked(self, *args):
        self._treeview.get_model().append([""])

    @Gtk.Template.Callback()
    def on_delete_button_clicked(self, *args):
        model, selected = self._treeview.get_selection().get_selected()

        model.remove(selected)

    @Gtk.Template.Callback()
    def on_treeview_selection_changed(self, *args):
        model, selected = self._treeview.get_selection().get_selected()

        self._btn_delete.set_sensitive(selected)

    @Gtk.Template.Callback()
    def on_text_edited(self, widget, path, text: str):
        self.model[path][0] = text
