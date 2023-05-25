from typing import Optional, Dict

from .json_conversion import as_json
from .Comorphism import Comorphism
from .Signature import Signature
from .HsWrapper import HsWrapper, HsHierarchyElement

from .haskell import comorphismNameOfGMorphism, comorphismDescriptionOfGMorphism, signatureOfGMorphism, comorphismOfGMorphism, \
    domainOfGMorphism, codomainOfGMorphism, isGMorphismInclusion, gMorphismToTransportType


class GMorphism:

    def __init__(self, hs_g_morphism) -> None:
        self._hs_g_morphism = hs_g_morphism

    def name(self) -> str:
        return comorphismNameOfGMorphism(self._hs_g_morphism)

    def description(self) -> str:
        return comorphismDescriptionOfGMorphism(self._hs_g_morphism)

    def signature(self) -> Signature:
        return Signature(signatureOfGMorphism(self._hs_g_morphism))

    def comorphism(self) -> Comorphism:
        return Comorphism(comorphismOfGMorphism(self._hs_g_morphism))

    def domain(self) -> dict:
        return as_json(domainOfGMorphism(self._hs_g_morphism))

    def codomain(self) -> dict:
        return as_json(codomainOfGMorphism(self._hs_g_morphism))

    def is_inclusion(self) -> bool:
        return isGMorphismInclusion(self._hs_g_morphism)

    def as_json(self) -> dict:
        return as_json(gMorphismToTransportType(self._hs_g_morphism))

    def symbol_map(self) -> Dict[object, object]:
        pass

