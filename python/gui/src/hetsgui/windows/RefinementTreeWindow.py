import logging


import hets

from gi.repository import Gtk

from hets.RefinementTree import RefinementTreeLinkKind
from ..GtkSmartTemplate import GtkSmartTemplate
from ..formatting import COLOR_MAP
from ..widgets import ExtendedDotWidget


@GtkSmartTemplate
class RefinementTreeWindow(Gtk.Window):
    __gtype_name__ = "RefinementTreeWindow"

    _logger = logging.getLogger(__name__)
    _ui_graph: ExtendedDotWidget = Gtk.Template.Child()
    _library: hets.Library
    _refinement_tree: hets.RefinementTree
    _spec_name: str

    def __init__(self, library: hets.Library, spec_name: str, **kwargs):
        super().__init__(**kwargs)
        self._library = library
        self._spec_name = spec_name

        self._refinement_tree = self._library.get_refinement_tree(spec_name)

        self._ui_graph.set_dotcode(self.get_graph().encode("utf-8"))

        self._ui_graph.connect("node-right-click", self._on_node_right_clicked)

    def get_graph(self, ):
        g = self._ui_graph.get_themed_graph()
        for node in self._refinement_tree.nodes():
            g.node(str(node.id()),
                   label=node.name(),
                   fillcolor=COLOR_MAP[("blue" if node.is_root() else "green", True, True)],
                   style="filled")

        for edge in self._refinement_tree.edges():
            black = COLOR_MAP[("black", False, False)]
            coral = COLOR_MAP[("coral", False, False)]
            color = {
                RefinementTreeLinkKind.SIMPLE: f"{black}:invis:{black}",
                RefinementTreeLinkKind.COMPONENT: black,
                RefinementTreeLinkKind.UNKNOWN: black,
            }[edge.kind()]

            g.edge(str(edge.source_id()), str(edge.target_id()), color=color)

        return g.source

    def _on_node_right_clicked(self, widget, node_id: str, event):
        pass
        # model = Gio.Menu()
        #
        # menu_item_open_ref = Gio.MenuItem()
        # menu_item_open_ref.set_label("Open library")
        # menu_item_open_ref.set_action_and_target_value("app.open_win_for_lib", get_variant(node_id))
        # model.append_item(menu_item_open_ref)
        #
        # menu = Gtk.Menu.new_from_model(model)
        # menu.attach_to_widget(self)
        # menu.show_all()
        # menu.popup(None, None, None, None, event.button, event.time)
