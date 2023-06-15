from typing import Optional

import graphviz
import xdot.ui.elements
from gi.repository import Gtk, Gio, GLib, Gdk
from graphviz import Graph, Digraph
from xdot import DotWidget

from hets import DevelopmentGraph, DevGraphNode, DevGraphEdge, TheoremDevGraphEdge, EdgeKind, DefinitionDevGraphEdge
from utils import get_variant


def node_shape(node: DevGraphNode) -> str:
    if node.is_reference_node():
        return "rectangle"
    else:
        return "ellipse"


def node_color(node: DevGraphNode) -> str:
    if node.is_proven_node():
        if node.is_consistency_proven():
            return "limegreen"
        else:
            return "gold2"
    else:
        return "coral"


def edge_color(edge: DevGraphEdge) -> str:
    if isinstance(edge, TheoremDevGraphEdge):
        if edge.is_proven():
            if edge.is_conservativ():
                color = "limegreen"
            else:
                color = "gold2"
        else:
            color = "coral"

    else:
        color = {
            EdgeKind.FREE: "royalblue",
            EdgeKind.COFREE: "royalblue",
            EdgeKind.HIDING: "royalblue",

            # default
            EdgeKind.LOCAL: "black",
            EdgeKind.GLOBAL: "black",

            # error
            EdgeKind.UNKNOWN: "fuchsia"
        }[edge.kind()]

    # Double lines for heterogeneous signature morphisms
    if edge.is_homogeneous():
        return color
    else:
        return f"{color}:invis:{color}"


def edge_style(edge: DevGraphEdge):
    # Note: Double lines are created with a color list. See edge_color
    if (isinstance(edge, TheoremDevGraphEdge) and edge.is_homogeneous() or isinstance(edge, DefinitionDevGraphEdge)) and edge.kind() == EdgeKind.LOCAL:
        return "dashed"
    else:
        return ""


class GraphvizGraphWidget(DotWidget):
    g: Optional[Digraph]
    development_graph: Optional[DevelopmentGraph]

    # View properties
    _show_internal_node_names: bool = False
    _show_unnamed_nodes_without_open_proofs: bool = False
    _show_newly_added_proven_edges: bool = False

    def __init__(self):
        super().__init__()
        self.g = None
        self.development_graph = None

    def load_graph(self, graph: DevelopmentGraph):
        self.development_graph = graph
        self.g = Digraph("G")

        self.render(False)

    def show_internal_node_names(self):
        self._show_internal_node_names = True
        self.render()

    def hide_internal_node_names(self):
        self._show_internal_node_names = False
        self.render()

    def show_unnamed_nodes_without_open_proofs(self):
        self._show_unnamed_nodes_without_open_proofs = True
        self.render()

    def hide_unnamed_nodes_without_open_proofs(self):
        self._show_unnamed_nodes_without_open_proofs = False
        self.render()

    def show_newly_added_proven_edges(self):
        self._show_newly_added_proven_edges = True
        self.render()

    def hide_newly_added_proven_edges(self):
        self._show_newly_added_proven_edges = False
        self.render()

    def render(self, keep_zoom=True) -> None:
        g = Digraph("G")

        for node in self.development_graph.nodes():
            g.node(str(node.id()),
                   label="" if node.is_internal() and not self._show_internal_node_names else node.name(),
                   fillcolor=node_color(node),
                   shape=node_shape(node),
                   style="filled")

        for edge in self.development_graph.edges():
            g.edge(str(edge.origin()), str(edge.target()),
                   style=edge_style(edge),
                   color=edge_color(edge),
                   label=edge.name())

        zoom_ration, x, y = self.zoom_ratio, self.x, self.y
        self.set_dotcode(g.source.encode("utf-8"))
        if keep_zoom:
            self.zoom_ratio, self.x, self.y = zoom_ration, x, y

        self.g = g

    def _menu_for_node(self, node_id: str) -> Gtk.Menu:
        menu = Gio.Menu()

        menu_item_prove = Gio.MenuItem()
        menu_item_prove.set_label("Prove")
        menu_item_prove.set_action_and_target_value("win.node.prove", GLib.Variant.new_string(node_id))
        menu.append_item(menu_item_prove)

        menu_item_info = Gio.MenuItem()
        menu_item_info.set_label("Show node info")
        menu_item_info.set_action_and_target_value("win.node.show_info", GLib.Variant.new_string(node_id))
        menu.append_item(menu_item_info)


        return Gtk.Menu.new_from_model(menu)

    def _menu_for_edge(self, src_id: str, dst_id: str) -> Gtk.Menu:
        menu = Gio.Menu()

        menu_item_info = Gio.MenuItem()
        menu_item_info.set_label("Show edge info")
        menu_item_info.set_action_and_target_value("win.edge.show_info", get_variant([src_id, dst_id]))
        menu.append_item(menu_item_info)


        return Gtk.Menu.new_from_model(menu)

    def on_draw(self, widget, cr):
        cr.set_source_rgb(1, 1, 1)
        cr.paint()

        return super().on_draw(widget, cr)

    def on_click(self, element, event):
        if element is None:
            return True

        if event.button == 3:  # on right click
            menu = None
            if isinstance(element, xdot.ui.elements.Node):
                node_id = element.id.decode("utf-8")

                menu = self._menu_for_node(node_id)
            if isinstance(element, xdot.ui.elements.Edge):
                src_id, dst_id = element.src.id.decode("utf-8"), element.dst.id.decode("utf-8")

                menu = self._menu_for_edge(src_id, dst_id)

            if menu:
                menu.attach_to_widget(self)
                # menu.add(menuItem2)
                menu.show_all()
                menu.popup(None, None, None, None, event.button, event.time)

        return True
        # return super().on_click(element, event)

    def on_area_motion_notify(self, area, event):
        return super().on_area_motion_notify(area, event)

    def set_highlight(self, items, search=False):
        super().set_highlight(items, search)

