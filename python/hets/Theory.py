from typing import List, Optional, Tuple

from .HsWrapper import HsHierarchyElement
from .haskell import (Just, Nothing, fst, thd, PyTheory, usableProvers, usableConsistencyCheckers, proveNodeAndRecord,
                      availableComorphisms, getAllSentences, getAllGoals, getAllAxioms, getProvenGoals, prettySentence,
                      getUnprovenGoals, OMap, fstOf3, sndOf3, ProofStatus, PyProver, PyComorphism, PyConsChecker,
                      ConsistencyStatus, defaultProofOptions, PyProofOptions, mkPyProofOptions, TheoryPointer, snd,
                      defaultConsCheckingOptions, PyConsCheckingOptions, checkConsistencyAndRecord)

from .result import resultOrRaise

from .Prover import Prover
from .ConsistencyChecker import ConsistencyChecker
from .Comorphism import Comorphism
from .ProofState import ProofState
from .Sentence import Sentence


class Theory(HsHierarchyElement):
    def __init__(self, hsTheory: PyTheory, parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)
        self._hsTheory = hsTheory
        self._hsPrettySentence = prettySentence(hsTheory)

    def hsObj(self):
        return self._hsTheory

    def hsUpdate(self, newHsObj):
        self._hsTheory = newHsObj

    def _theoryPointer(self) -> TheoryPointer:
        node = self.parent().hsObj()
        graph = self.parent().parent().hsObj()
        envName = self.parent().parent().parent().hsObj()

        name = fst(envName)
        env = snd(envName)

        return name, env, graph, node

    def usableProvers(self) -> List[Prover]:
        provers = usableProvers(self._hsTheory).act()
        return list({Prover(fst(p)) for p in provers})

    def usableConsistencyCheckers(self) -> List[ConsistencyChecker]:
        ccs = usableConsistencyCheckers(self._hsTheory).act()
        return list({ConsistencyChecker(fst(cc)) for cc in ccs})

    def availableComorphisms(self) -> List[Comorphism]:
        comorphisms = availableComorphisms(self._hsTheory)
        return [Comorphism(x) for x in comorphisms]

    def prove(self,
              prover: Optional[Prover] = None,
              comorphism: Optional[Comorphism] = None,
              useTheorems: Optional[bool] = None,
              goalsToProve: Optional[List[str]] = None,
              axiomsToInclude: Optional[List[str]] = None,
              timeout: Optional[int] = None
              ) -> List[ProofStatus]:
        proverM = Just(prover._hsProver) if prover else Nothing().subst(a=PyProver())
        comorphismM = Just(comorphism._hsComorphism) if comorphism else Nothing().subst(a=PyComorphism())

        defaultOpts = defaultProofOptions

        opts = mkPyProofOptions(
            proverM,
            comorphismM)(
            useTheorems if useTheorems is not None else defaultOpts.proofOptsUseTheorems(),
            goalsToProve if goalsToProve is not None else defaultOpts.proofOptsGoalsToProve(),
            axiomsToInclude if axiomsToInclude is not None else defaultOpts.proofOptsAxiomsToInclude(),
            timeout if timeout is not None else defaultOpts.proofOptsTimeout(),
        )

        proveResultR = proveNodeAndRecord(self._theoryPointer(), opts).act()
        result = resultOrRaise(proveResultR)
        newThAndStatuses = fst(result)
        newTh = fst(newThAndStatuses)
        goalStatuses = snd(newThAndStatuses)
        newEnv = snd(result)

        self.hsUpdate(newTh)

        self.root().hsUpdate(newEnv)

        return goalStatuses

    def checkConsistency(self,
                         consChecker: Optional[ConsistencyChecker] = None,
                         comorphism: Optional[Comorphism] = None,
                         includeTheorems: Optional[bool] = None,
                         timeout: Optional[int] = None
                         ) -> ConsistencyStatus:
        ccM = Just(consChecker._hsConsChecker) if consChecker else Nothing().subst(a=PyConsChecker())
        comorphismM = Just(comorphism._hsComorphism) if comorphism else Nothing().subst(a=PyComorphism())

        defaultOpts = defaultConsCheckingOptions

        opts = PyConsCheckingOptions(
            ccM,
            comorphismM,
            includeTheorems if includeTheorems is not None else defaultOpts.consOptsIncludeTheorems(),
            timeout if timeout is not None else defaultOpts.consOptsTimeout(),
        )

        result = checkConsistencyAndRecord(self._theoryPointer(), opts).act()
        ccResult, newEnv = fst(result), snd(result)

        self.root().hsUpdate(newEnv)

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
