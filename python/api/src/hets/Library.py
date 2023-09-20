"""
Description :  Represents `(Common.LibName.LibName, Static.DevGraph.LibEnv)`
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Optional, Dict, Any, Tuple, List

from .DevelopmentGraph import DevelopmentGraph
from .HsWrapper import HsHierarchyElement
from .Options import Options
from .haskell import loadLibrary as loadHsLibrary, fst, snd, getGraphForLibrary, Result, resultToMaybe, Just, fromJust, \
    automatic as automaticHs, globalSubsume as globalSubsumeHs, globalDecomposition as globalDecompositionHs, \
    localInference as localInferenceHs, localDecomposition as localDecompositionHs, \
    compositionProveEdges as compositionProveEdgesHs, conservativity as conservativityHs, \
    automaticHideTheoremShift as automaticHideTheoremShiftHs, theoremHideShift as theoremHideShiftHs, \
    computeColimit as computeColimitHs, normalForm as normalFormHs, triangleCons as triangleConsHs, \
    freeness as freenessHs, libFlatImports as libFlatImportsHs, libFlatDUnions as libFlatDUnionsHs, \
    libFlatRenamings as libFlatRenamingsHs, libFlatHiding as libFlatHidingHs, libFlatHeterogen as libFlatHeterogenHs, \
    qualifyLibEnv as qualifyLibEnvHs, LibName as HsLibName
from .result import result_or_raise
from .LibName import LibName


class Library(HsHierarchyElement):
    def __init__(self, hs_library) -> None:
        super().__init__(None)
        # if isinstance(hs_library, tuple):
        #     self._name = hs_library[0]
        #     self._env = hs_library[1]
        # else:
        self._name = fst(hs_library)
        self._env = snd(hs_library)

        self._dgraph: Optional[DevelopmentGraph] = None
        self._referenced_libraries = {}

    def hs_obj(self):
        return self._name, self._env

    def hs_update(self, new_env):
        self._env = new_env

        if self._dgraph:
            hs_graph = getGraphForLibrary(self._name, self._env)
            self._dgraph.hs_update(hs_graph)

        for lib in self._referenced_libraries.values():
            lib.hs_update(new_env)

    def referenced_library(self, name: LibName):
        if name not in self._referenced_libraries:
            self._referenced_libraries[name] = Library((name._hs_libname, self._env))

        return self._referenced_libraries[name]

    def name(self) -> LibName:
        return LibName(self._name)

    def development_graph(self) -> DevelopmentGraph:
        if self._dgraph is None:
            self._dgraph = DevelopmentGraph(getGraphForLibrary(self._name, self._env), self)

        return self._dgraph

    def environment(self) -> List[Tuple[LibName, DevelopmentGraph]]:
        hs_dict: List[Tuple[Any, Any]] = self._env.toList()

        return [(LibName(n), DevelopmentGraph(g, self)) for n,g in hs_dict]

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
        new_env_r = theoremHideShiftHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def compute_colimit(self):
        new_env_r = computeColimitHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def normal_form(self):
        new_env_r = normalFormHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def triangle_cons(self):
        new_env_r = triangleConsHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def freeness(self):
        new_env_r = freenessHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_imports(self):
        new_env_r = libFlatImportsHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_d_unions(self):
        new_env_r = libFlatDUnionsHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_renamings(self):
        new_env_r = libFlatRenamingsHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_hiding(self):
        new_env_r = libFlatHidingHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def lib_flat_heterogen(self):
        new_env_r = libFlatHeterogenHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def qualify_lib_env(self):
        new_env_r = qualifyLibEnvHs(self._name, self._env)
        self.hs_update_result(new_env_r)

    def hs_update_result(self, new_env_r: Result):
        new_env_m = resultToMaybe(new_env_r)
        if isinstance(new_env_m, Just):
            self.hs_update(fromJust(new_env_m))


def load_library(path: str, options: Optional[Options] = None) -> Library:
    if options is None:
        options = Options()

    result = loadHsLibrary(path, options._hs_options).act()

    name_and_env = result_or_raise(result, "Failed to load library")

    return Library(name_and_env)
