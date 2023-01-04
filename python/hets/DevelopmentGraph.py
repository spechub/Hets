
from typing import List, Optional, Tuple

import hyphen
from hs.Hets.Python import (PyTheory, autoProveNode, availableComorphisms,
                            getLNodesFromDevelopmentGraph, getTheoryFromNode,
                            usableConsistencyCheckers, usableProvers, thd)
from hs.Prelude import Just, Nothing, fst, snd
from hs.Static.DevGraph import DevGraph
from .result import resultOrRaise

class Axiom:
    pass

class Goal:
    pass

class ProofState:
    pass


class ProofTree:
    pass


class ConsistencyChecker:
    pass


class Comorphism:
    pass


class Prover:
    pass


class Theory:
    def __init__(self, hsTheory: PyTheory) -> None:
        self._hsTheory = hsTheory

    def usableProvers(self) -> List[Prover]:
        provers = usableProvers(self._hsTheory).act()
        # Todo: Extract actual provers and link to comorphisms
        return [Prover(x) for x in provers]

    def usableConsistencyCheckers(self) -> List[ConsistencyChecker]:
        ccs = usableConsistencyCheckers(self._hsTheory).act()
        return [ConsistencyChecker(x) for x in ccs]

    def availableComorphisms(self) -> List[Comorphism]:
        comorphisms = availableComorphisms(self._hsTheory)
        return [Comorphism(x) for x in comorphisms]

    def prove(self, prover: Optional[Prover] = None, comorphism: Optional[Comorphism] = None) -> Tuple[ProofState, ProofTree]:
        proverM = Just(prover) if prover else Nothing()
        comorphismM = Just(comorphism) if comorphism else Nothing()

        proveResultR = autoProveNode(
            self._hsTheory, proverM, comorphismM).act()
        proveResult = resultOrRaise(proveResultR)

        self._hsTheory = fst(proveResult)

        state = snd(proveResult)
        tree = thd(proveResult)

        return ProofState(state), ProofTree(tree)
    
    def axioms(self) -> List[Axiom]:
        pass
    
    def goals(self) -> List[Goal]:
        pass


class DevGraphNode:
    def __init__(self, hsNode) -> None:
        self._hsNode = hsNode

    def theory(self) -> Theory:
        Theory(getTheoryFromNode(self._hsNode))


class DevelopmentGraph:
    def __init__(self, hsDevelopmentGraph: DevGraph) -> None:
        self._hsDevelopmentGraph = hsDevelopmentGraph

    def nodes(self) -> List[DevGraphNode]:
        hsNodes = getLNodesFromDevelopmentGraph(self._hsDevelopmentGraph)
        return [DevGraphNode(x) for x in hsNodes]
