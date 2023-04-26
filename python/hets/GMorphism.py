from typing import Optional

from .Comorphism import Comorphism
from .Signature import Signature
from .HsWrapper import HsWrapper, HsHierarchyElement

from .haskell import logicNameOfGMorphism, logicDescriptionOfGMorphism, signatureOfGMorphism, comorphismOfGMorphism


class GMorphism:

    def __init__(self, hs_g_morphism) -> None:
        self._hs_g_morphism = hs_g_morphism

    def name(self) -> str:
        return logicNameOfGMorphism(self._hs_g_morphism)

    def description(self) -> str:
        return logicDescriptionOfGMorphism(self._hs_g_morphism)

    def signature(self) -> Signature:
        return Signature(signatureOfGMorphism(self._hs_g_morphism))

    def comorphism(self) -> Comorphism:
        return Comorphism(comorphismOfGMorphism(self._hs_g_morphism))
