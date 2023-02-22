from .haskell import defaultHetcatsOpts, loadLibrary, fst, snd, getGraphForLibrary, HetcatsOpts, autoCheckConsistency

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


class Library:
    def __init__(self, path: str, options: HetcatsOpts = defaultHetcatsOpts) -> None:
        resultR = loadLibrary(path, options).act()

        nameAndEnv = resultOrRaise(resultR, "Failed to load library")
        self._name = fst(nameAndEnv)
        self._env = snd(nameAndEnv)

    def getDevelopmentGraph(self) -> DevelopmentGraph:
        return DevelopmentGraph(getGraphForLibrary(self._name, self._env), autoCheckConsistency(self._name, self._env))

    def automatic(self):
        self._env = automaticHs(self._name, self._env)

    def globalSubsume(self):
        self._env = globalSubsumeHs(self._name, self._env)

    def globalDecomposition(self):
        self._env = globalDecompositionHs(self._name, self._env)

    def localInference(self):
        self._env = localInferenceHs(self._name, self._env)

    def localDecomposition(self):
        self._env = localDecompositionHs(self._name, self._env)

    def compositionProveEdges(self):
        self._env = compositionProveEdgesHs(self._name, self._env)

    def conservativity(self):
        self._env = conservativityHs(self._name, self._env)

    def automaticHideTheoremShift(self):
        self._env = automaticHideTheoremShiftHs(self._name, self._env)

    def theoremHideShift(self):
        self._env = theoremHideShiftHs(self._name, self._env)

    def computeColimit(self):
        self._env = computeColimitHs(self._name, self._env)

    def normalForm(self):
        self._env = normalFormHs(self._name, self._env)

    def triangleCons(self):
        self._env = triangleConsHs(self._name, self._env)

    def freeness(self):
        self._env = freenessHs(self._name, self._env)

    def libFlatImports(self):
        self._env = libFlatImportsHs(self._name, self._env)

    def libFlatDUnions(self):
        self._env = libFlatDUnionsHs(self._name, self._env)

    def libFlatRenamings(self):
        self._env = libFlatRenamingsHs(self._name, self._env)

    def libFlatHiding(self):
        self._env = libFlatHidingHs(self._name, self._env)

    def libFlatHeterogen(self):
        self._env = libFlatHeterogenHs(self._name, self._env)

    def qualifyLibEnv(self):
        self._env = qualifyLibEnvHs(self._name, self._env)
