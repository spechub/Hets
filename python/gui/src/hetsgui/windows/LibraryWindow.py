import logging

from graphviz import Digraph

import hets

from gi.repository import Gtk, Gio, GLib

from ..GtkSmartTemplate import GtkSmartTemplate
from ..formatting import COLOR_MAP
from ..utils import get_variant
from ..widgets import ExtendedDotWidget




@GtkSmartTemplate
class LibraryWindow(Gtk.Window):
    __gtype_name__ = "LibraryWindow"

    _logger = logging.getLogger(__name__)
    _ui_graph: ExtendedDotWidget = Gtk.Template.Child()
    _library: hets.Library

    def __init__(self, library: hets.Library, **kwargs):
        super().__init__(**kwargs)
        self._library = library

        self._ui_graph.set_dotcode(self.get_graph().encode("utf-8"))

        self._ui_graph.connect("node-right-click", self._on_node_right_clicked)

    def get_graph(self,):
        g = self._ui_graph.get_themed_graph()
        for name, _ in self._library.environment():
            g.node(name.id(), label=str(name),
                   fillcolor=COLOR_MAP[("green", True, True)],
                   style="filled",
                   shape="rectangle")

        for source, target in self._library.dependencies():
            g.edge(source.id(), target.id())

        return g.source

    def _on_node_right_clicked(self, widget, node_id: str, event):
        model = Gio.Menu()

        menu_item_open_ref = Gio.MenuItem()
        menu_item_open_ref.set_label("Open library")
        menu_item_open_ref.set_action_and_target_value("app.open_win_for_lib", get_variant(node_id))
        model.append_item(menu_item_open_ref)

        menu = Gtk.Menu.new_from_model(model)
        menu.attach_to_widget(self)
        menu.show_all()
        menu.popup(None, None, None, None, event.button, event.time)
