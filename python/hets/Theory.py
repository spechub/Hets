from typing import List, Optional, Tuple

from .haskell import (Just, Nothing, fst, thd, PyTheory, usableProvers, usableConsistencyCheckers, autoProveNode,
                      availableComorphisms, getAllSentences, getAllGoals, getAllAxioms, getProvenGoals, prettySentence,
                      getUnprovenGoals, OMap, fstOf3, sndOf3, ProofStatus, PyProver, PyComorphism, PyConsChecker,
                      ConsistencyStatus)

from .result import resultOrRaise

from .Prover import Prover
from .ConsistencyChecker import ConsistencyChecker
from .Comorphism import Comorphism
from .ProofState import ProofState
from .Sentence import Sentence


class Theory:
    def __init__(self, hsTheory: PyTheory, hsAutoCheckConsistency) -> None:
        self._hsTheory = hsTheory
        self._hsPrettySentence = prettySentence(hsTheory)
        self._hsAutoCheckConsistency = hsAutoCheckConsistency

    def usableProvers(self) -> List[Prover]:
        provers = usableProvers(self._hsTheory).act()
        return list({Prover(fst(p)) for p in provers})

    def usableConsistencyCheckers(self) -> List[ConsistencyChecker]:
        ccs = usableConsistencyCheckers(self._hsTheory).act()
        return list({ConsistencyChecker(fst(cc)) for cc in ccs})

    def availableComorphisms(self) -> List[Comorphism]:
        comorphisms = availableComorphisms(self._hsTheory)
        return [Comorphism(x) for x in comorphisms]

    def prove(self, prover: Optional[Prover] = None, comorphism: Optional[Comorphism] = None) -> Tuple[
        ProofState, List[ProofStatus]]:
        proverM = Just(prover._hsProver) if prover else Nothing().subst(a=PyProver())
        comorphismM = Just(comorphism._hsComorphism) if comorphism else Nothing().subst(a=PyComorphism())

        proveResultR = autoProveNode(
            self._hsTheory, proverM, comorphismM).act()
        proveResult = resultOrRaise(proveResultR)

        self._hsTheory = fstOf3(proveResult)

        state = sndOf3(proveResult)
        status = thd(proveResult)

        return ProofState(state, self), status

    def checkConsistency(self, consChecker: Optional[ConsistencyChecker] = None,
                         comorphism: Optional[Comorphism] = None, includeTheorems: Optional[bool] = True,
                         timeout: Optional[int] = 600) -> ConsistencyStatus:
        ccM = Just(consChecker._hsConsChecker) if consChecker else Nothing().subst(a=PyConsChecker())
        comorphismM = Just(comorphism._hsComorphism) if comorphism else Nothing().subst(a=PyComorphism())

        ccResult = self._hsAutoCheckConsistency(timeout, includeTheorems, ccM, comorphismM).act()

        return ccResult

    def sentences(self) -> List[Sentence]:
        sentences = getAllSentences(self._hsTheory)
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(sentences)]

    def axioms(self) -> List[Sentence]:
        axioms = getAllAxioms(self._hsTheory)
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(axioms)]

    def goals(self) -> List[Sentence]:
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(getAllGoals(self._hsTheory))]

    def provenGoals(self) -> List[Sentence]:
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(getProvenGoals(self._hsTheory))]

    def unprovenGoals(self) -> List[Sentence]:
        return [Sentence(x, self._hsPrettySentence) for x in OMap.toList(getUnprovenGoals(self._hsTheory))]
