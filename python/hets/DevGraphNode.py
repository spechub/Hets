from typing import Tuple, Optional, List

from .ConsistencyStatus import ConsistencyStatus
from .Comorphism import Comorphism
from .result import resultOrRaise
from .ConsistencyChecker import ConsistencyChecker
from .ProofStatus import ProofStatus
from .Prover import Prover
from .HsWrapper import HsHierarchyElement
from .haskell import snd, getTheoryFromNode, DGNodeLab, fst, Just, Nothing, PyProver, PyComorphism, defaultProofOptions, \
    mkPyProofOptions, proveNodeAndRecord, ConsistencyStatus as HsConsistencyStatus, PyConsChecker, \
    defaultConsCheckingOptions, \
    PyConsCheckingOptions, checkConsistencyAndRecord, TheoryPointer, getGlobalTheory, recomputeNode, fromJust

from .Theory import Theory


class DevGraphNode(HsHierarchyElement):
    def __init__(self, hsNode: Tuple[int, DGNodeLab], parent: Optional[HsHierarchyElement]) -> None:
        super().__init__(parent)

        self._hsNode = hsNode

        self._theory: Optional[Theory] = None

    def hsObj(self):
        return self._hsNode

    def id(self) -> int:
        return fst(self._hsNode)

    def label(self) -> DGNodeLab:
        return snd(self._hsNode)

    def name(self) -> str:
        return self.label().dgn_name()

    def _theoryPointer(self) -> TheoryPointer:
        node = self.hsObj()
        graph = self.parent().hsObj()
        envName = self.parent().parent().hsObj()

        name = fst(envName)
        env = snd(envName)

        return name, env, graph, node

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
        goalStatuses = snd(newThAndStatuses)
        newEnv = snd(result)

        self.root().hsUpdate(newEnv)

        return goalStatuses

    def checkConsistency(self,
                         consChecker: Optional[ConsistencyChecker] = None,
                         comorphism: Optional[Comorphism] = None,
                         includeTheorems: Optional[bool] = None,
                         timeout: Optional[int] = None
                         ) -> HsConsistencyStatus:
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


    def consistencyStatus(self) -> ConsistencyStatus:
        nodeLab = snd(self._hsNode)
        hsConsStatus = nodeLab.getNodeConsStatus()
        return ConsistencyStatus(hsConsStatus)

    def globalTheory(self) -> Optional[Theory]:
        nodeLab = snd(self._hsNode)

        pyTheoryM = getGlobalTheory(nodeLab)

        if isinstance(pyTheoryM, Just):
            pyTheory = fromJust(pyTheoryM)
            return Theory(pyTheory, self)

        return None

    def recompute(self) -> None:
        newLibEnv = recomputeNode(self._theoryPointer())

        root = self.parent().parent()
        root.hsUpdate(newLibEnv)

    def hsUpdate(self, newHsObj):
        self._hsNode = newHsObj

        if self._theory:
            nodeLab = snd(self._hsNode)
            hsTheory = getTheoryFromNode(nodeLab)
            self._theory.hsUpdate(hsTheory)

    def theory(self) -> Theory:
        if self._theory is None:
            self._theory = Theory(getTheoryFromNode(snd(self._hsNode)), self)

        return self._theory
