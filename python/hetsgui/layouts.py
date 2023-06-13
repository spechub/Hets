from typing import List

import numpy as np
from graph_tool import ungroup_vector_property, group_vector_property
from graph_tool.topology import topological_sort

import graph_tool as gt

from numpy import sqrt

from grandalf.layouts import SugiyamaLayout
from grandalf.graphs import Vertex, Edge, Graph, graph_core


class defaultview(object):
    w, h = 10, 10
    xy: List[int]


def hierarchical_layout(g: gt.Graph, sizes, shape=None, dim=2, pos=None):
    # if pos is None:
    pos = g.new_vertex_property("vector<double>")

    vertices: List[gt.Vertex] = list(g.vertices())
    edges: List[gt.Edge] = list(g.edges())

    V = [Vertex(v) for v in vertices]

    def node(v):
        return next(a for a in V if a.data == v)

    E = [Edge(node(e.source()), node(e.target())) for e in edges]
    g = Graph(V, E)

    for v in V:
        v.view = defaultview()
        v.view.w = sizes[v.data][0]
        v.view.h = sizes[v.data][1]

    for C in g.C:
        sug = SugiyamaLayout(C)
        sug.init_all()
        sug.draw()

        for v in C.sV:
            print("%s: (%d,%d)" % (v.data, v.view.xy[0], v.view.xy[1]))

            v_id = v.data
            pos[v_id] = v.view.xy

    return pos
