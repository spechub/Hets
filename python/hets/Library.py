from typing import Optional

from .HsWrapper import HsWrapper, HsHierarchyElement
from .haskell import defaultHetcatsOpts, loadLibrary as loadHsLibrary, fst, snd, getGraphForLibrary, HetcatsOpts, checkConsistencyAndRecord

from .DevelopmentGraph import DevelopmentGraph
from .result import resultOrRaise

from .haskell import (
    automatic as automaticHs,
    globalSubsume as globalSubsumeHs,
    globalDecomposition as globalDecompositionHs,
    localInference as localInferenceHs,
    localDecomposition as localDecompositionHs,
    compositionProveEdges as compositionProveEdgesHs,
    conservativity as conservativityHs,
    automaticHideTheoremShift as automaticHideTheoremShiftHs,
    theoremHideShift as theoremHideShiftHs,
    computeColimit as computeColimitHs,
    normalForm as normalFormHs,
    triangleCons as triangleConsHs,
    freeness as freenessHs,
    libFlatImports as libFlatImportsHs,
    libFlatDUnions as libFlatDUnionsHs,
    libFlatRenamings as libFlatRenamingsHs,
    libFlatHiding as libFlatHidingHs,
    libFlatHeterogen as libFlatHeterogenHs,
    qualifyLibEnv as qualifyLibEnvHs
)


class Library(HsHierarchyElement):
    def __init__(self, hsLibrary) -> None:
        super().__init__(None)
        self._name = fst(hsLibrary)
        self._env = snd(hsLibrary)

        self._dgraph: Optional[DevelopmentGraph] = None

    def hsObj(self):
        return self._name, self._env

    def hsUpdate(self, newEnv):
        self._env = newEnv

        if self._dgraph:
            hsGraph = getGraphForLibrary(self._name, self._env)
            self._dgraph.hsUpdate(hsGraph)

    def getDevelopmentGraph(self) -> DevelopmentGraph:
        if self._dgraph is None:
            self._dgraph = DevelopmentGraph(getGraphForLibrary(self._name, self._env), self)

        return self._dgraph

    def automatic(self):
        newEnv = automaticHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def globalSubsume(self):
        newEnv = globalSubsumeHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def globalDecomposition(self):
        newEnv = globalDecompositionHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def localInference(self):
        newEnv = localInferenceHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def localDecomposition(self):
        newEnv = localDecompositionHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def compositionProveEdges(self):
        newEnv = compositionProveEdgesHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def conservativity(self):
        newEnv = conservativityHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def automaticHideTheoremShift(self):
        newEnv = automaticHideTheoremShiftHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def theoremHideShift(self):
        newEnv = theoremHideShiftHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def computeColimit(self):
        newEnv = computeColimitHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def normalForm(self):
        newEnv = normalFormHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def triangleCons(self):
        newEnv = triangleConsHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def freeness(self):
        newEnv = freenessHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def libFlatImports(self):
        newEnv = libFlatImportsHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def libFlatDUnions(self):
        newEnv = libFlatDUnionsHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def libFlatRenamings(self):
        newEnv = libFlatRenamingsHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def libFlatHiding(self):
        newEnv = libFlatHidingHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def libFlatHeterogen(self):
        newEnv = libFlatHeterogenHs(self._name, self._env)
        self.hsUpdate(newEnv)

    def qualifyLibEnv(self):
        newEnv = qualifyLibEnvHs(self._name, self._env)
        self.hsUpdate(newEnv)

def loadLibrary(path: str, options: HetcatsOpts = defaultHetcatsOpts) -> Library:
    result = loadHsLibrary(path, options).act()

    nameAndEnv = resultOrRaise(result, "Failed to load library")

    return Library(nameAndEnv)