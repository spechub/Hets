import logging
import threading
from typing import Optional, Tuple

import xdot.ui.elements
from gi.repository import Gtk, Gio, GLib, GObject
from graphviz import Digraph
from xdot import DotWidget

from formatting.colors import color_to_hex
from hets import DevelopmentGraph, DevGraphNode, DevGraphEdge, TheoremDevGraphEdge, EdgeKind
from utils import get_variant
from .ExtendedDotWidget import ExtendedDotWidget

# KEY: (colorname, variant, light)
COLOR_MAP = {
    ("black", False, False): "gray0"
    , ("black", False, True): "gray30"
    , ("blue", False, False): "RoyalBlue3"
    , ("blue", False, True): "RoyalBlue1"
    , ("blue", True, False): "SteelBlue3"
    , ("blue", True, True): "SteelBlue1"
    , ("coral", False, False): "coral3"
    , ("coral", False, True): "coral1"
    , ("coral", True, False): "LightSalmon2"
    , ("coral", True, True): "LightSalmon"
    , ("green", False, False): "MediumSeaGreen"
    , ("green", False, True): "PaleGreen3"
    , ("green", True, False): "limegreen"
    , ("green", True, True): "LightGreen"
    , ("purple", False, False): "purple2"
    , ("yellow", False, False): "gold"
    , ("yellow", False, True): "yellow"
    , ("yellow", True, False): "LightGoldenrod3"
    , ("yellow", True, True): "LightGoldenrod"
    , ("fuchsia", False, False): "fuchsia"
    , ("fuchsia", False, True): "fuchsia"
    , ("fuchsia", True, False): "fuchsia"
    , ("fuchsia", True, True): "fuchsia"
}


def node_shape(node: DevGraphNode) -> str:
    if node.is_reference_node():
        return "rectangle"
    else:
        return "ellipse"


def node_color(node: DevGraphNode) -> str:
    if node.is_proven_node():
        if node.is_consistency_proven():
            return COLOR_MAP[("green", True, False)]
        else:
            return COLOR_MAP[("yellow", False, True)]
    else:
        return COLOR_MAP[("coral", False, node.is_consistency_proven())]


def edge_color(edge: DevGraphEdge) -> str:
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

    final_color = COLOR_MAP[(color_name, color_use_variant, color_use_light)]

    # Double lines for heterogeneous signature morphisms
    if edge.is_homogeneous():
        return final_color
    else:
        return f"{final_color}:invis:{final_color}"


def edge_style(edge: DevGraphEdge):
    # Note: Double lines are created with a color list. See edge_color
    if isinstance(edge, TheoremDevGraphEdge) and edge.kind() == EdgeKind.LOCAL:
        return "dashed"
    else:
        return ""


class GraphvizGraphWidget(ExtendedDotWidget):
    __gtype_name__ = "GraphvizGraphWidget"

    __gsignals__ = {
        "render-start": (GObject.SIGNAL_RUN_FIRST, None, ()),
        "render-end": (GObject.SIGNAL_RUN_FIRST, None, ())
    }

    _logger = logging.getLogger(__name__)

    g: Optional[Digraph]
    development_graph: Optional[DevelopmentGraph]

    _render_thread: Optional[threading.Thread]

    # View properties
    _show_internal_node_names: bool = False
    _show_newly_added_proven_edges: bool = False

    def __init__(self):
        super().__init__()
        self._render_thread = None
        self.g = None
        self.development_graph = None

        self._dot_code = None

        settings: Gtk.Settings = Gtk.Settings.get_for_screen(self.get_screen())
        settings.connect("notify::gtk-theme-name", lambda w, p: self.render())
        settings.connect("notify::gtk-application-prefer-dark-theme", lambda w, p: self.render())

    def load_graph(self, graph: DevelopmentGraph):
        self._logger.debug("Loading graph")
        self.development_graph = graph
        self.g = Digraph("G")

        self.render(False)

    def show_internal_node_names(self):
        self._logger.debug("Show internal nodes")
        self._show_internal_node_names = True
        self.render()

    def hide_internal_node_names(self):
        self._logger.debug("Hide internal nodes")
        self._show_internal_node_names = False
        self.render()

    def show_newly_added_proven_edges(self):
        self._logger.debug("Show newly added proven edges")
        self._show_newly_added_proven_edges = True
        self.render()

    def hide_newly_added_proven_edges(self):
        self._logger.debug("Hide newly added proven edges")
        self._show_newly_added_proven_edges = False
        self.render()

    def _render(self, keep_zoom, color) -> None:
        self._logger.debug("Render graph; keep zoom: %s", keep_zoom)
        GLib.idle_add(lambda: self.emit("render-start"))
        g = Digraph("G")

        if color:
            g.graph_attr["bgcolor"] = color

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
                   label=edge.name())

        zoom_ration, x, y = self.zoom_ratio, self.x, self.y
        dot_code = g.source

        if dot_code != self._dot_code:
            self.set_dotcode(dot_code.encode("utf-8"))
            if keep_zoom:
                self.zoom_ratio, self.x, self.y = zoom_ration, x, y
        else:
            self._logger.debug("Dot code did not change. Do not call graphviz")

        self.g = g

        GLib.idle_add(lambda: self.emit("render-end"))

    def render(self, keep_zoom=True) -> None:
        if self._render_thread and self._render_thread.is_alive():
            self._logger.debug("Already rendering. Waiting for previous render to finish")
            self._render_thread.join()

        success, color = self.get_style_context().lookup_color("theme_bg_color")
        color = color_to_hex(color)

        self._render_thread = threading.Thread(target=self._render, args=[keep_zoom, color])
        self._render_thread.start()

    def _menu_for_node(self, node_id: str) -> Gtk.Menu:
        menu = Gio.Menu()

        menu_item_prove = Gio.MenuItem()
        menu_item_prove.set_label("Prove")
        menu_item_prove.set_action_and_target_value("win.node.prove", GLib.Variant.new_string(node_id))
        menu.append_item(menu_item_prove)

        menu_item_consistency = Gio.MenuItem()
        menu_item_consistency.set_label("Check consistency")
        menu_item_consistency.set_action_and_target_value("win.node.check_consistency",
                                                          GLib.Variant.new_string(node_id))
        menu.append_item(menu_item_consistency)

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

    def on_click(self, element, event):
        if element is None:
            jump = self.get_jump(event.x, event.y)
            element = jump.item if jump is not None else None

        if element is None:
            return True

        if event.button == 3:  # on right click
            self._logger.debug("Right click on %s", element)
            menu = None
            if isinstance(element, xdot.ui.elements.Node):
                node_id = element.id.decode("utf-8")

                menu = self._menu_for_node(node_id)
            elif isinstance(element, xdot.ui.elements.Edge):
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
