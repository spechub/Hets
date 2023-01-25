
from typing import List, Optional, Tuple

import hyphen
from hs.Hets.Python import (PyTheory, autoProveNode, availableComorphisms,
                            getLNodesFromDevelopmentGraph, getTheoryFromNode,
                            usableConsistencyCheckers, usableProvers, thd,
                            getAllSentences, getAllAxioms, getAllGoals,
                            getProvenGoals, getUnprovenGoals, getProverName,
                            getComorphismName, getConsCheckerName)
from hs.Prelude import Just, Nothing, fst, snd, show
from hs.Static.DevGraph import DevGraph
import hs.Common.OrderedMap as OMap
from .result import resultOrRaise


class Sentence:
    def __init__(self, hsSentenceWithName) -> None:
        self._name = fst(hsSentenceWithName)
        self._hsSentence = snd(hsSentenceWithName)

    def name(self) -> str:
        return self._name

    def __str__(self) -> str:
        return show(self._hsSentence)


class ProofState:
    pass


class ProofTree:
    pass


class ConsistencyChecker:
    def __init__(self, hsConsChecker) -> None:
        self._hsConsChecker = hsConsChecker

    def name(self) -> str:
        return getConsCheckerName(self._hsConsChecker)


class Comorphism:
    def __init__(self, hsComorphism) -> None:
        self._hsComorphism = hsComorphism

    def name(self) -> str:
        return getComorphismName(self._hsComorphism)


class Prover:
    def __init__(self, hsProver) -> None:
        self._hsProver = hsProver

    def name(self) -> str:
        return getProverName(self._hsProver)


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

    def sentences(self) -> List[Sentence]:
        return [Sentence(x) for x in OMap.toList(getAllSentences(self._hsTheory))]

    def axioms(self) -> List[Sentence]:
        return [Sentence(x) for x in OMap.toList(getAllAxioms(self._hsTheory))]

    def goals(self) -> List[Sentence]:
        return [Sentence(x) for x in OMap.toList(getAllGoals(self._hsTheory))]

    def provenGoals(self) -> List[Sentence]:
        return [Sentence(x) for x in OMap.toList(getProvenGoals(self._hsTheory))]

    def unprovenGoals(self) -> List[Sentence]:
        return [Sentence(x) for x in OMap.toList(getUnprovenGoals(self._hsTheory))]


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
