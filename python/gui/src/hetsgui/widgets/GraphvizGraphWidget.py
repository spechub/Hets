import logging
import threading
from collections import defaultdict
from typing import Optional, Tuple, DefaultDict

from gi.repository import Gtk, Gio, GLib, GObject
from graphviz import Digraph

from ..formatting.colors import COLOR_MAP
from ..formatting.colors import color_to_hex
from hets import DevelopmentGraph, DevGraphNode, DevGraphEdge, TheoremDevGraphEdge, EdgeKind, ConsistencyKind
from ..utils import get_variant
from .ExtendedDotWidget import ExtendedDotWidget


def node_shape(node: DevGraphNode) -> str:
    """
    Get the shape of a node based on its type.
    :param node: The node
    :return: 'rectangle' or 'ellipse'
    """

    if node.is_reference_node():
        return "rectangle"
    else:
        return "ellipse"


def node_color(node: DevGraphNode) -> str:
    """
    Get the color of a node based on its type.
    :param node: The node
    :return: The color
    """
    if node.is_proven_node():
        if node.is_consistency_proven():
            return COLOR_MAP[("green", True, False)]
        else:
            return COLOR_MAP[("yellow", False, True)]
    else:
        return COLOR_MAP[("coral", False, node.is_consistency_proven())]


def edge_color(edge: DevGraphEdge) -> str:
    """
    Get the color of an edge based on its type.

    :param edge: The edge
    :return: The color
    """

    color: Tuple[str, bool] = ("fuchsia", True)  # (color name, use variant)
    if isinstance(edge, TheoremDevGraphEdge):
        if not edge.is_proven():
            if edge.kind() == EdgeKind.LOCAL and not edge.is_homogeneous():
                color = ("coral", True)
                # coral true
            elif edge.kind() == EdgeKind.HIDING:
                color = ("yellow", False)
            else:
                color = ("coral", False)
        elif not edge.is_conservativ():
            if edge.kind() == EdgeKind.LOCAL and not edge.is_homogeneous():
                color = ("yellow", True)
            else:
                color = ("yellow", False)
        elif edge.is_pending():
            if edge.kind() == EdgeKind.LOCAL and not edge.is_homogeneous():
                color = ("yellow", True)
            else:
                color = ("yellow", False)
        else:
            if edge.kind() == EdgeKind.LOCAL and not edge.is_homogeneous():
                color = ("green", True)
            elif edge.kind() == EdgeKind.HIDING:
                color = ("green", True)
            else:
                color = ("green", False)

    else:
        color = {
            EdgeKind.FREE: ("blue", False),
            EdgeKind.COFREE: ("blue", False),
            EdgeKind.HIDING: ("blue", False),

            # default
            EdgeKind.LOCAL: ("black", False),
            EdgeKind.GLOBAL: ("black", False),

            # error
            EdgeKind.UNKNOWN: ("fuchsia", False)
        }[edge.kind()]

    color_name, color_use_variant = color
    color_use_light = not edge.is_inclusion()

    # Resolve the color map.
    final_color = COLOR_MAP[(color_name, color_use_variant, color_use_light)]

    # Double lines for heterogeneous signature morphisms
    if edge.is_homogeneous():
        return final_color
    else:
        return f"{final_color}:invis:{final_color}"


def edge_label(edge: DevGraphEdge) -> str:
    """
    Get the label of an edge based on its type.
    :param edge:
    :return:
    """

    status = edge.conservativity_status()
    cons_required = status.required()
    cons_proven = status.proven()
    if cons_required == cons_proven == ConsistencyKind.NONE or cons_required == ConsistencyKind.NONE and not status.is_proven_link():
        return ""

    if status.is_proven_link():
        return cons_proven.short_name()
    else:
        return cons_required.short_name() + "?"


def edge_style(edge: DevGraphEdge):
    # Note: Double lines are created with a color list. See edge_color
    if isinstance(edge, TheoremDevGraphEdge) and edge.kind() == EdgeKind.LOCAL:
        return "dashed"
    else:
        return ""


class GraphvizGraphWidget(ExtendedDotWidget):
    """
    An extended DotWidget that can render a DevelopmentGraph.
    """

    __gtype_name__ = "GraphvizGraphWidget"

    __gsignals__ = {
        "render-start": (GObject.SIGNAL_RUN_FIRST, None, ()),
        "render-end": (GObject.SIGNAL_RUN_FIRST, None, ())
    }

    _logger = logging.getLogger(__name__)

    g: Optional[Digraph]
    """ The graphviz graph to be rendered. """

    development_graph: Optional[DevelopmentGraph]
    """
    The development graph to be visualised.
    """

    _render_thread: Optional[threading.Thread]
    """
    The thread that calculates the dot code of the graph in the background.
    """

    # View properties
    _show_internal_node_names: bool = False
    _show_newly_added_proven_edges: bool = False

    def set_graph_direction(self, value: str):
        self._render_graph_vertical = value
        if self.graph:
            self.render(False)

    def get_graph_direction(self) -> str:
        return self._render_graph_vertical

    graph_direction = property(fset=set_graph_direction, fget=get_graph_direction)
    """
    The direction the graph should be rendered (allowed values: 'vertical', 'horizontal').
    """

    def __init__(self):
        super().__init__()
        self._render_thread = None
        self.g = None
        self.development_graph = None
        self.graph_direction = "vertical"

        self._dot_code = None

    def do_node_right_click(self, node: str, event):
        self._on_node_clicked(node, event)

    def do_edge_right_click(self, src: str, dest: str, event):
        self._on_edge_clicked(src, dest, event)

    def load_graph(self, graph: DevelopmentGraph):
        """
        Loads and renders a development graph.

        :param graph: The graph to be loaded
        :return:
        """

        self._logger.debug("Loading graph")
        self.development_graph = graph
        self.g = Digraph("G")

        self.render(False)

    def show_internal_node_names(self):
        """
        Show the names of internal nodes.

        .. seealso:: hide_internal_node_names

        :return:
        """

        self._logger.debug("Show internal nodes")
        self._show_internal_node_names = True
        self.render()

    def hide_internal_node_names(self):
        """
        Hide the names of internal nodes.

        .. seealso:: show_internal_node_names

        :return:
        """

        self._logger.debug("Hide internal nodes")
        self._show_internal_node_names = False
        self.render()

    def show_newly_added_proven_edges(self):
        """
        Show newly added proven edges.

        .. seealso:: hide_newly_added_proven_edges

        :return:
        """

        self._logger.debug("Show newly added proven edges")
        self._show_newly_added_proven_edges = True
        self.render()

    def hide_newly_added_proven_edges(self):
        """
        Hide newly added proven edges.

        .. seealso:: show_newly_added_proven_edges

        :return:
        """

        self._logger.debug("Hide newly added proven edges")
        self._show_newly_added_proven_edges = False
        self.render()

    def _render(self, keep_zoom: bool) -> None:
        """
        Renders the graph by computing the dot code and forwarding it to the xdot widget.

        Performs blocking operations and is intended to be executed in a background thread.

        :param keep_zoom: Whether to keep the current zoom level or reset it to 1
        :return:
        """
        if not self.development_graph:
            return

        self._logger.debug("Render graph; keep zoom: %s, direction: %s", keep_zoom, self.graph_direction)

        # Emit the render-start signal in the main thread
        GLib.idle_add(lambda: self.emit("render-start"))

        # Build the graph ...
        g = self.get_themed_graph()
        g.graph_attr["rankdir"] = "LR" if self.graph_direction == "horizontal" else "TB"

        for node in self.development_graph.nodes():
            g.node(str(node.id()),
                   label="" if node.is_internal() and not self._show_internal_node_names else node.name(),
                   fillcolor=node_color(node),
                   shape=node_shape(node),
                   style="filled")

        for edge in self.development_graph.edges():
            if not self._show_newly_added_proven_edges \
                    and isinstance(edge, TheoremDevGraphEdge) \
                    and edge.is_proven() \
                    and (edge.is_conservativ() or edge.kind() in [EdgeKind.HIDING, EdgeKind.FREE, EdgeKind.COFREE]):
                continue

            g.edge(str(edge.origin()), str(edge.target()),
                   style=edge_style(edge),
                   color=edge_color(edge),
                   label=edge_label(edge),
                   fontcolor="grey")

        zoom_ration, x, y = self.zoom_ratio, self.x, self.y
        dot_code = g.source

        if dot_code != self._dot_code:
            # Call graphviz to create dot code
            self.set_dotcode(dot_code.encode("utf-8"))
            if keep_zoom:
                self.zoom_ratio, self.x, self.y = zoom_ration, x, y
        else:
            self._logger.debug("Dot code did not change. Do not call graphviz")

        self.g = g

        # Emit the render-edn signal in the main thread
        GLib.idle_add(lambda: self.emit("render-end"))

    def render(self, keep_zoom: bool = True) -> None:
        """
        Renders the graph asynchrounsly in the background

        :param keep_zoom: Whether to keep the current zoom level or reset it to 1
        :return:
        """

        if self._render_thread and self._render_thread.is_alive():
            self._logger.debug("Already rendering. Waiting for previous render to finish")
            self._render_thread.join()

        self._render_thread = threading.Thread(target=self._render, args=[keep_zoom])
        self._render_thread.start()

    def _menu_for_node(self, node_id: str) -> Gtk.Menu:
        """
        Generate a context menu for a graph node

        :param node_id: The id of the node
        :return: The context menu
        """

        menu = Gio.Menu()

        node = self.development_graph.node_by_id(int(node_id))
        if node is None:
            self._logger.warning(
                f"Trying to open a menu for node {node_id} but the node was not found in the development graph")
            return menu

        menu_item_prove = Gio.MenuItem()
        menu_item_prove.set_label("Prove")
        menu_item_prove.set_action_and_target_value("win.node.prove", GLib.Variant.new_string(node_id))
        menu.append_item(menu_item_prove)

        menu_item_info = Gio.MenuItem()
        menu_item_info.set_label("Show node info")
        menu_item_info.set_action_and_target_value("win.node.show_info", GLib.Variant.new_string(node_id))
        menu.append_item(menu_item_info)

        menu_item_show_theory = Gio.MenuItem()
        menu_item_show_theory.set_label("Show theory")
        menu_item_show_theory.set_action_and_target_value("win.node.show_theory", GLib.Variant.new_string(node_id))
        menu.append_item(menu_item_show_theory)

        menu_translate = Gio.Menu()
        menus_by_target = dict()
        for c in node.global_theory().get_available_comorphisms():
            menu_item_comorphism = Gio.MenuItem()
            menu_item_comorphism.set_label(f"{c.target()} ({c.name()})")
            menu_item_comorphism.set_action_and_target_value("win.node.translate", get_variant((node_id, c.name())))

            menu_comorphism = menus_by_target.setdefault(c.target(), Gio.Menu())
            menu_comorphism.append_item(menu_item_comorphism)

        for k, v in menus_by_target.items():
            menu_item_comorphism = Gio.MenuItem()
            menu_item_comorphism.set_label(k)
            menu_item_comorphism.set_submenu(v)
            menu_translate.append_item(menu_item_comorphism)

        menu_item_translate = Gio.MenuItem()
        menu_item_translate.set_label("Translate theory")
        menu_item_translate.set_submenu(menu_translate)
        menu.append_item(menu_item_translate)

        if node.is_reference_node():
            menu_item_open_ref = Gio.MenuItem()
            menu_item_open_ref.set_label("Open " + node.name())
            menu_item_open_ref.set_action_and_target_value("win.open_win_for_lib_by_node",
                                                           GLib.Variant.new_int32(node.id()))
            menu.append_item(menu_item_open_ref)
        else:
            menu_item_consistency = Gio.MenuItem()
            menu_item_consistency.set_label("Check consistency")
            menu_item_consistency.set_action_and_target_value("win.node.check_consistency",
                                                              GLib.Variant.new_string(node_id))
            menu.append_item(menu_item_consistency)

        return Gtk.Menu.new_from_model(menu)

    def _menu_for_edge(self, src_id: str, dst_id: str) -> Gtk.Menu:
        """
        Generate a context menu for an edge

        :param src_id: id of the source node
        :param dst_id: id of the target node
        :return: The context menu
        """

        menu = Gio.Menu()

        menu_item_info = Gio.MenuItem()
        menu_item_info.set_label("Show edge info")
        menu_item_info.set_action_and_target_value("win.edge.show_info", get_variant((src_id, dst_id)))
        menu.append_item(menu_item_info)

        menu_item_consistency = Gio.MenuItem()
        menu_item_consistency.set_label("Check conservativity")
        menu_item_consistency.set_action_and_target_value("win.edge.check_conservativity",
                                                          get_variant((src_id, dst_id)))
        menu.append_item(menu_item_consistency)

        return Gtk.Menu.new_from_model(menu)

    def _on_node_clicked(self, node_id: str, event):
        """
        Handler of the right-click event on a node. Shows a context menu.

        :param node_id: id of the clicked node
        :param event: the event
        :return:
        """

        menu = self._menu_for_node(node_id)
        menu.attach_to_widget(self)
        menu.show_all()
        menu.popup(None, None, None, None, event.button, event.time)

    def _on_edge_clicked(self, src_id: str, dst_id: str, event):
        """
        Handler of the right-click event on an edge. Shows a context menu.
        :param src_id: id of the source node
        :param dst_id: id of the target node
        :param event: the event
        :return:
        """

        menu = self._menu_for_edge(src_id, dst_id)
        menu.attach_to_widget(self)
        menu.show_all()
        menu.popup(None, None, None, None, event.button, event.time)

    def on_area_motion_notify(self, area, event):
        # To be overwritten in the future ...
        return super().on_area_motion_notify(area, event)

    def set_highlight(self, items, search=False):
        # To be overwritten in the future ...
        super().set_highlight(items, search)
