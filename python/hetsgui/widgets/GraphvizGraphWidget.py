from typing import Optional

import graphviz
from gi.repository import Gtk, Gio
from graphviz import Graph, Digraph
from xdot import DotWidget

from hets import DevelopmentGraph, DevGraphNode, DevGraphEdge, TheoremDevGraphEdge, EdgeKind


def node_shape(node: DevGraphNode) -> str:
    if node.is_reference_node():
        return "rectangle"
    else:
        return "ellipse"


def node_color(node: DevGraphNode) -> str:
    if node.is_proven_node():
        if node.is_consistency_proven():
            return "green"
        else:
            return "yellow"
    else:
        return "coral"


def edge_color(edge: DevGraphEdge) -> str:
    if isinstance(edge, TheoremDevGraphEdge):
        if edge.is_proven():
            if edge.is_conservativ():
                color = "green"
            else:
                color = "yellow"
        else:
            color = "red"

    color = {
        EdgeKind.FREE: "blue",
        EdgeKind.COFREE: "blue",
        EdgeKind.HIDING: "blue",

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
    if isinstance(edge, TheoremDevGraphEdge):
        return "dashed"
    else:
        return ""


class GraphvizGraphWidget(DotWidget):
    g: Optional[Digraph]
    development_graph: Optional[DevelopmentGraph]

    def __init__(self):
        super().__init__()
        self.g = None
        self.development_graph = None

    def load_graph(self, graph: DevelopmentGraph):
        self.development_graph = graph
        self.g = Digraph("G")

        self.render()

    def render(self) -> None:
        g = Digraph("G")

        for node in self.development_graph.nodes():
            g.node(str(node.id()),
                   label="" if node.is_internal() else node.name(),
                   fillcolor=node_color(node),
                   shape=node_shape(node),
                   style="filled")

        for edge in self.development_graph.edges():
            g.edge(str(edge.origin()), str(edge.target()),
                   style=edge_style(edge),
                   color=edge_color(edge),
                   label=edge.name())

        self.set_dotcode(g.source.encode("utf-8"))

        self.g = g

    def on_draw(self, widget, cr):
        cr.set_source_rgb(1, 1, 1)
        cr.paint()

        return super().on_draw(widget, cr)

    def on_click(self, element, event):
        if element is None:
            return True

        if event.button == 3:  # on right click
            menu = Gtk.Menu()

            action_prove = Gtk.Action('prove-node')
            action_prove.connect('activate', self.on_prove_node)

            menu.append(Gtk.MenuItem("Prove", "prove-node"))

            # menuItem2 = Gtk.MenuItem(label="Create edge from" if self.new_edge_first_node_id is None else "Create edge to")

            # def onClick(menuItem):
            #     if self.new_edge_first_node_id is None:
            #         self.new_edge_first_node_id = element.id
            #         return
            #
            #     # Keep the positions of the previous nodes
            #     g = Digraph()
            #     g.node_attr["shape"] = "box"
            #
            #     first_node_id_b: bytes = self.new_edge_first_node_id
            #     first_node_id = first_node_id_b.decode("utf-8")
            #     second_node_id_b: bytes = element.id
            #     second_node_id = second_node_id_b.decode("utf-8")
            #
            #     # g.node(str(new_node_id), label=f"New Node #{new_node_id}", group=f"g{new_node_id}")
            #     g.edge(first_node_id, second_node_id)
            #
            #     for n in self.graph.nodes:
            #         id = int(n.id.decode("utf-8"))
            #         if n.id in [first_node_id_b, second_node_id_b]:
            #             g.node(n.id.decode("utf-8"), label=self.nodes[id], fillcolor='green', style='filled',
            #                    pos=f"{n.x},{n.y}!")
            #         else:
            #             g.node(n.id.decode("utf-8"), label=self.nodes[id],
            #                    pos=f"{n.x},{n.y}!")
            #
            #     for o, t in self.edges:
            #         g.edge(str(o), str(t))
            #
            #     self.edges.append((int(first_node_id), int(second_node_id)))
            #
            #     print(g.source)
            #
            #     pos_x, pos_y = self.get_current_pos()
            #     ratio = self.zoom_ratio
            #     # self.set_filter("fdp")
            #     self.set_dotcode(g.source.encode("utf-8"))
            #     self.set_current_pos(pos_x, pos_y)
            #     self.zoom_image(ratio)
            #
            #     self.g = g
            #     self.new_edge_first_node_id = None

            # menuItem2.connect("activate", onClick)

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

    def on_prove_node(self, action, value):
        print('Action: {}\nValue: {}'.format(action, value))








