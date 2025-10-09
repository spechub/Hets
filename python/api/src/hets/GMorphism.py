from typing import Optional, Dict

from .json_conversion import as_json
from .Comorphism import Comorphism
from .Signature import Signature
from .HsWrapper import HsWrapper, HsHierarchyElement

from .haskell import comorphismNameOfGMorphism, comorphismDescriptionOfGMorphism, signatureOfGMorphism, comorphismOfGMorphism, \
    domainOfGMorphism, codomainOfGMorphism, isGMorphismInclusion, gMorphismToTransportType


class GMorphism:
    """
    Represents a Grothendieck signature morphisms with indices.

    Represents `Logic.Grothendieck.GMorphism` via `HetsAPI.Python.PyGMorphism`.
    """

    def __init__(self, hs_g_morphism) -> None:
        self._hs_g_morphism = hs_g_morphism

    def name(self) -> str:
        """
        Returns the name of the morphism.
        :return:
        """
        return comorphismNameOfGMorphism(self._hs_g_morphism)

    def description(self) -> str:
        """
        Returns the description of the morphism.
        :return:
        """
        return comorphismDescriptionOfGMorphism(self._hs_g_morphism)

    def signature(self) -> Signature:
        """
        Returns the signature of the morphism.
        :return:
        """
        return Signature(signatureOfGMorphism(self._hs_g_morphism))

    def comorphism(self) -> Comorphism:
        """
        Returns the comorphism of the morphism.
        :return:
        """
        return Comorphism(comorphismOfGMorphism(self._hs_g_morphism))

    def domain(self) -> dict:
        """
        Returns the domain of the morphism.
        :return:
        """
        return as_json(domainOfGMorphism(self._hs_g_morphism))

    def codomain(self) -> dict:
        """
        Returns the codomain of the morphism.
        :return:
        """
        return as_json(codomainOfGMorphism(self._hs_g_morphism))

    def is_inclusion(self) -> bool:
        """
        Returns whether the morphism is an inclusion.
        :return:
        """
        return isGMorphismInclusion(self._hs_g_morphism)

    def as_json(self) -> dict:
        """
        Returns the morphism as a json object.
        :return:
        """
        return as_json(gMorphismToTransportType(self._hs_g_morphism))

    def symbol_map(self) -> Dict[object, object]:
        pass

