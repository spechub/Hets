"""
Description :  Represents `Static.DevGraph.DGraph`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
from typing import List, Optional

from .DevGraphNode import DevGraphNode
from .DevGraphEdge import DevGraphEdge, DefinitionDevGraphEdge, TheoremDevGraphEdge
from .GlobalAnnotations import GlobalAnnotations
from .HsWrapper import HsHierarchyElement

from .haskell import getLNodesFromDevelopmentGraph, DGraph, Nothing, fromJust, getDGNodeById, \
    getLEdgesFromDevelopmentGraph, globalAnnotations, getDevGraphLinkType, thd, DefinitionLink


class DevelopmentGraph(HsHierarchyElement):
    def __init__(self, hs_development_graph: DGraph, parent: HsHierarchyElement) -> None:
        super().__init__(parent)

        self._hs_development_graph = hs_development_graph

        self._nodes: Optional[List[DevGraphNode]] = None
        self._edges: Optional[List[DevGraphEdge]] = None

    def hs_obj(self):
        return self._hs_development_graph

    def hs_update(self, new_hs_obj: DGraph):
        self._hs_development_graph = new_hs_obj

        if self._nodes:
            for node in self._nodes:
                hs_node_maybe = getDGNodeById(self._hs_development_graph)(node.id())
                if isinstance(hs_node_maybe, Nothing):
                    print(f"Node {node.id} could not be found. Probably, it has been deleted")
                else:
                    hsNode = fromJust(hs_node_maybe)
                    node.hs_update((node.id(), hsNode))

    def nodes(self) -> List[DevGraphNode]:
        if self._nodes is None:
            hs_nodes = getLNodesFromDevelopmentGraph(self._hs_development_graph)
            self._nodes = [DevGraphNode(x, self) for x in hs_nodes]

        return self._nodes

    def edges(self) -> List[DevGraphEdge]:
        hs_edges = getLEdgesFromDevelopmentGraph(self._hs_development_graph)

        return [DefinitionDevGraphEdge(x, self) if isinstance(getDevGraphLinkType(thd(x)), DefinitionLink) else TheoremDevGraphEdge(x, self) for x in hs_edges]

    def global_annotations(self) -> GlobalAnnotations:
        return GlobalAnnotations(globalAnnotations(self._hs_development_graph))
