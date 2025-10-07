import logging


import hets

from gi.repository import Gtk

from hets.RefinementTreeLink import RefinementTreeLinkKind
from ..GtkSmartTemplate import GtkSmartTemplate
from ..formatting import COLOR_MAP
from ..widgets import ExtendedDotWidget


@GtkSmartTemplate
class RefinementTreeWindow(Gtk.Window):
    """
    A window to show a refinement tree.
    """
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
        """
        Create a graphviz graph of the refinement tree.
        :return:
        """
        g = self._ui_graph.get_themed_graph()
        for node in self._refinement_tree.nodes():
            g.node(str(node.id()),
                   label=node.name(),
                   fillcolor=COLOR_MAP[("blue" if node.is_root() else "green", True, True)],
                   style="filled")

        for edge in self._refinement_tree.edges():
            black = COLOR_MAP[("black", False, False)]
            color = {
                RefinementTreeLinkKind.SIMPLE: f"{black}:invis:{black}",
                RefinementTreeLinkKind.COMPONENT: black,
                RefinementTreeLinkKind.UNKNOWN: black,
            }[edge.kind()]

            g.edge(str(edge.source_id()), str(edge.target_id()), color=color)

        return g.source

    def _on_node_right_clicked(self, widget, node_id: str, event):
        pass