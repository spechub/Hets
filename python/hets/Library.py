"""
Description :  Represents `(Common.LibName.LibName, Static.DevGraph.LibEnv)`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Optional

from .HsWrapper import HsWrapper, HsHierarchyElement
from .haskell import defaultHetcatsOpts, loadLibrary as loadHsLibrary, fst, snd, getGraphForLibrary, HetcatsOpts, \
    checkConsistencyAndRecord

from .DevelopmentGraph import DevelopmentGraph
from .result import result_or_raise

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
    def __init__(self, hs_library) -> None:
        super().__init__(None)
        self._name = fst(hs_library)
        self._env = snd(hs_library)

        self._dgraph: Optional[DevelopmentGraph] = None

    def hs_obj(self):
        return self._name, self._env

    def hs_update(self, new_env):
        self._env = new_env

        if self._dgraph:
            hs_graph = getGraphForLibrary(self._name, self._env)
            self._dgraph.hs_update(hs_graph)

    def development_graph(self) -> DevelopmentGraph:
        if self._dgraph is None:
            self._dgraph = DevelopmentGraph(getGraphForLibrary(self._name, self._env), self)

        return self._dgraph

    def automatic(self):
        new_env = automaticHs(self._name, self._env)
        self.hs_update(new_env)

    def global_subsume(self):
        new_env = globalSubsumeHs(self._name, self._env)
        self.hs_update(new_env)

    def global_decomposition(self):
        new_env = globalDecompositionHs(self._name, self._env)
        self.hs_update(new_env)

    def local_inference(self):
        new_env = localInferenceHs(self._name, self._env)
        self.hs_update(new_env)

    def local_decomposition(self):
        new_env = localDecompositionHs(self._name, self._env)
        self.hs_update(new_env)

    def composition_prove_edges(self):
        new_env = compositionProveEdgesHs(self._name, self._env)
        self.hs_update(new_env)

    def conservativity(self):
        new_env = conservativityHs(self._name, self._env)
        self.hs_update(new_env)

    def automatic_hide_theorem_shift(self):
        new_env = automaticHideTheoremShiftHs(self._name, self._env)
        self.hs_update(new_env)

    def theorem_hide_shift(self):
        new_env = theoremHideShiftHs(self._name, self._env)
        self.hs_update(new_env)

    def compute_colimit(self):
        new_env = computeColimitHs(self._name, self._env)
        self.hs_update(new_env)

    def normal_form(self):
        new_env = normalFormHs(self._name, self._env)
        self.hs_update(new_env)

    def triangle_cons(self):
        new_env = triangleConsHs(self._name, self._env)
        self.hs_update(new_env)

    def freeness(self):
        new_env = freenessHs(self._name, self._env)
        self.hs_update(new_env)

    def lib_flat_imports(self):
        new_env = libFlatImportsHs(self._name, self._env)
        self.hs_update(new_env)

    def lib_flat_d_unions(self):
        new_env = libFlatDUnionsHs(self._name, self._env)
        self.hs_update(new_env)

    def lib_flat_renamings(self):
        new_env = libFlatRenamingsHs(self._name, self._env)
        self.hs_update(new_env)

    def lib_flat_hiding(self):
        new_env = libFlatHidingHs(self._name, self._env)
        self.hs_update(new_env)

    def lib_flat_heterogen(self):
        new_env = libFlatHeterogenHs(self._name, self._env)
        self.hs_update(new_env)

    def qualify_lib_env(self):
        new_env = qualifyLibEnvHs(self._name, self._env)
        self.hs_update(new_env)


def load_library(path: str, options: HetcatsOpts = defaultHetcatsOpts) -> Library:
    result = loadHsLibrary(path, options).act()

    name_and_env = result_or_raise(result, "Failed to load library")

    return Library(name_and_env)
