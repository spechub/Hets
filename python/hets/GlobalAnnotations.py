from .haskell import precedenceAnnotations, associativityAnnotations, displayAnnos, literalAnnos, prefixMap


class GlobalAnnotations:
    def __init__(self, hs_global_annos):
        self._hs_global_annos = hs_global_annos

    def precedence_annotations(self) -> object:
        """
        Returns the precedence annotations.
        WARNING! This functions returns a plain hyphen (haskell) object. Interaction might be difficult.

        @return: Plain hyphen object of the precedence annotations
        """
        return precedenceAnnotations(self._hs_global_annos)

    def associativity_annotations(self) -> dict:
        """
        Returns the associativity annotations.
        WARNING! This functions returns a plain hyphen (haskell) object. Interaction might be difficult.

        @return: Plain hyphen object of the associativity annotations
        """
        return associativityAnnotations(self._hs_global_annos)

    def display_annos(self) -> dict:
        """
        Returns a map on how to display ids according to a format.
        WARNING! This functions returns a plain hyphen (haskell) object. Interaction might be difficult.

        @return: Plain hyphen object of the display map
        """
        return displayAnnos(self._hs_global_annos)

    def literal_annos(self) -> object:
        """
        Returns the literal map.
        WARNING! This functions returns a plain hyphen (haskell) object. Interaction might be difficult.

        @return: Plain hyphen object of the literal map
        """
        return literalAnnos(self._hs_global_annos)

    def prefix_map(self) -> dict:
        """
        Returns a prefix definitions as map from prefix to definition.
        WARNING! This functions returns a plain hyphen (haskell) object. Interaction might be difficult.

        @return: Plain hyphen object of the prefix map
        """
        return prefixMap(self._hs_global_annos)

