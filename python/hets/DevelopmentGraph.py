from typing import List
from .DevGraphNode import DevGraphNode

from .haskell import getLNodesFromDevelopmentGraph, DGraph


class DevelopmentGraph:
    def __init__(self, hsDevelopmentGraph: DGraph, hsAutoCheckConsistency) -> None:
        self._hsDevelopmentGraph = hsDevelopmentGraph
        self._hsAutoCheckConsistency = hsAutoCheckConsistency(hsDevelopmentGraph)

    def nodes(self) -> List[DevGraphNode]:
        hsNodes = getLNodesFromDevelopmentGraph(self._hsDevelopmentGraph)
        return [DevGraphNode(x, self._hsAutoCheckConsistency) for x in hsNodes]
