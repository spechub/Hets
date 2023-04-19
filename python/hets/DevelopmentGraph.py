"""
Description :  Represents `Static.DevGraph.DGraph`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""
from typing import List, Optional

from .DevGraphNode import DevGraphNode
from .DevGraphEdge import DevGraphEdge
from .HsWrapper import HsHierarchyElement

from .haskell import getLNodesFromDevelopmentGraph, DGraph, Nothing, fromJust, getDGNodeById, \
    getLEdgesFromDevelopmentGraph


class DevelopmentGraph(HsHierarchyElement):
    def __init__(self, hsDevelopmentGraph: DGraph, parent: HsHierarchyElement) -> None:
        super().__init__(parent)

        self._hsDevelopmentGraph = hsDevelopmentGraph

        self._nodes: Optional[List[DevGraphNode]] = None
        self._edges: Optional[List[DevGraphEdge]] = None

    def hsObj(self):
        return self._hsDevelopmentGraph

    def hsUpdate(self, newHsObj: DGraph):
        self._hsDevelopmentGraph = newHsObj

        if self._nodes:
            for node in self._nodes:
                hsNodeM = getDGNodeById(self._hsDevelopmentGraph, node.id())
                if isinstance(hsNodeM, Nothing):
                    print(f"Node {node.id} could not be found. Probably, it has been deleted")
                else:
                    hsNode = fromJust(hsNodeM)
                    node.hsUpdate((node.id(), hsNode))

    def nodes(self) -> List[DevGraphNode]:
        if self._nodes is None:
            hsNodes = getLNodesFromDevelopmentGraph(self._hsDevelopmentGraph)
            self._nodes = [DevGraphNode(x, self) for x in hsNodes]

        return self._nodes

    def edges(self) -> List[DevGraphEdge]:
        if self._edges is None:
            hsEdges = getLEdgesFromDevelopmentGraph(self._hsDevelopmentGraph)
            self._edges = [DevGraphEdge(x, self) for x in hsEdges]

        return self._edges

