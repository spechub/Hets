from typing import List, Optional

from .DevGraphNode import DevGraphNode
from .HsWrapper import HsHierarchyElement

from .haskell import getLNodesFromDevelopmentGraph, DGraph, Nothing, fromJust, getDGNodeById


class DevelopmentGraph(HsHierarchyElement):
    def __init__(self, hsDevelopmentGraph: DGraph, parent: HsHierarchyElement) -> None:
        super().__init__(parent)

        self._hsDevelopmentGraph = hsDevelopmentGraph

        self._nodes: Optional[List[DevGraphNode]] = None

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

