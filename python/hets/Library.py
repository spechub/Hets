import hyphen
import hs.Hets.Pyton
from hs.Common.Result import resultToMaybe
from hs.Hets.Python import defaultHetcatsOpts, loadLibrary
from hs.Prelude import Just, fromJust, fst, show, snd

from .result import resultOrRaise


class Library:    
    def __init__(self, path: str, options = defaultHetcatsOpts) -> None:
        resultR = loadLibrary(path, options).act()
        
        nameAndEnv = resultOrRaise(resultR, "Failed to load library")
        self._name = fst(nameAndEnv)
        self._env = snd(nameAndEnv)
        
    def automatic(self):
        self._env = hs.Hets.Python.automatic(self._name, self._env)

    def globalSubsume(self):
        self._env = hs.Hets.Python.globalSubsume(self._name, self._env)

    def globalDecomposition(self):
        self._env = hs.Hets.Python.globalDecomposition(self._name, self._env)

    def localInference(self):
        self._env = hs.Hets.Python.localInference(self._name, self._env)

    def localDecomposition(self):
        self._env = hs.Hets.Python.localDecomposition(self._name, self._env)

    def compositionProveEdges(self):
        self._env = hs.Hets.Python.compositionProveEdges(self._name, self._env)

    def conservativity(self):
        self._env = hs.Hets.Python.conservativity(self._name, self._env)

    def automaticHideTheoremShift(self):
        self._env = hs.Hets.Python.automaticHideTheoremShift(self._name, self._env)

    def theoremHideShift(self):
        self._env = hs.Hets.Python.theoremHideShift(self._name, self._env)

    def computeColimit(self):
        self._env = hs.Hets.Python.computeColimit(self._name, self._env)

    def normalForm(self):
        self._env = hs.Hets.Python.normalForm(self._name, self._env)

    def triangleCons(self):
        self._env = hs.Hets.Python.triangleCons(self._name, self._env)

    def freeness(self):
        self._env = hs.Hets.Python.freeness(self._name, self._env)

    def libFlatImports(self):
        self._env = hs.Hets.Python.libFlatImports(self._name, self._env)

    def libFlatDUnions(self):
        self._env = hs.Hets.Python.libFlatDUnions(self._name, self._env)

    def libFlatRenamings(self):
        self._env = hs.Hets.Python.libFlatRenamings(self._name, self._env)

    def libFlatHiding(self):
        self._env = hs.Hets.Python.libFlatHiding(self._name, self._env)

    def libFlatHeterogen(self):
        self._env = hs.Hets.Python.libFlatHeterogen(self._name, self._env)

    def qualifyLibEnv(self):
        self._env = hs.Hets.Python.qualifyLibEnv(self._name, self._env)

        
    