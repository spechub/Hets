import logging
import typing
from typing import List, Optional, Dict

from .DevGraphNode import DevGraphNode, dev_graph_node_from_hs
from .DevGraphEdge import DevGraphEdge, DefinitionDevGraphEdge, TheoremDevGraphEdge
from .GlobalAnnotations import GlobalAnnotations
from .HsWrapper import HsHierarchyElement

from .haskell import getLNodesFromDevelopmentGraph, DGraph, Nothing, Just, fromJust, getDGNodeById, \
    getLEdgesFromDevelopmentGraph, globalAnnotations, getDevGraphLinkType, thd, DefinitionLink, fst


class DevelopmentGraph(HsHierarchyElement):
    """
    Represents a development graph.

    Represents `Static.DevGraph.DGraph`
    """

    _logger = logging.getLogger(__name__)

    def __init__(self, hs_development_graph: DGraph, parent: HsHierarchyElement) -> None:
        super().__init__(parent)

        self._hs_development_graph = hs_development_graph

        self._nodes: Optional[Dict[int, DevGraphNode]] = None
        self._edges: Optional[List[DevGraphEdge]] = None

    def hs_obj(self):
        """
        Returns the underlying Haskell object.
        :return:
        """

        return self._hs_development_graph

    def hs_update(self, new_hs_obj: DGraph):
        self._hs_development_graph = new_hs_obj
        self._logger.debug("Updating hs object of development graph")

        if self._nodes:
            for node_id, node in self._nodes.items():
                hs_node_maybe = getDGNodeById(self._hs_development_graph)(node_id)
                if isinstance(hs_node_maybe, Nothing):
                    self._logger.warning(f"Node {node_id} could not be found. Probably, it has been deleted")
                else:
                    hsNode = fromJust(hs_node_maybe)
                    node.hs_update((node_id, hsNode))

    def nodes(self) -> List[DevGraphNode]:
        """
        Get all nodes in the development graph.
        :return: List of nodes
        """
        if self._nodes is None:
            hs_nodes = getLNodesFromDevelopmentGraph(self._hs_development_graph)
            self._nodes = dict((fst(x), dev_graph_node_from_hs(x, self)) for x in hs_nodes)

        return list(self._nodes.values())

    def node_by_id(self, node_id: int) -> Optional[DevGraphNode]:
        """
        Get a node by its id.
        :param node_id: Id of the node
        :return: Node if found, otherwise None
        """
        if self._nodes is None:
            self._nodes = {}

        self._logger.debug("Get node %s in %s", node_id, self._nodes)

        if node_id not in self._nodes:
            hs_node_maybe = getDGNodeById(self._hs_development_graph)(node_id)
            if isinstance(hs_node_maybe, Just):
                hs_node = fromJust(hs_node_maybe)
                node = dev_graph_node_from_hs(hs_node, self)
                self._nodes[node_id] = node

        return self._nodes.get(node_id, None)

    def edges(self) -> List[DevGraphEdge]:
        """
        Get all edges in the development graph.
        :return: List of edges
        """
        hs_edges = getLEdgesFromDevelopmentGraph(self._hs_development_graph)

        return [DefinitionDevGraphEdge(x, self) if isinstance(getDevGraphLinkType(thd(x)), DefinitionLink) else TheoremDevGraphEdge(x, self) for x in hs_edges]

    def global_annotations(self) -> GlobalAnnotations:
        """
        Get the global annotations of the development graph.
        :return:
        """
        return GlobalAnnotations(globalAnnotations(self._hs_development_graph))
