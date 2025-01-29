from typing import Optional


class HsWrapper:
    """
    Base class for wrapped Haskell elements.

    Offers a common base class for treating immutable Haskell objects as mutable Python objects.
    """

    def hs_obj(self):
        """
        Derived classes should implement this function to return the underlying Haskell object.
        :return: The underlying Haskell object
        """
        pass

    def hs_update(self, new_hs_obj):
        """
        Derived classes should implement this function to facilitate a Python mutable object by updating the underlying
        Haskell object.

        :param new_hs_obj: New Haskell object
        :return:
        """
        pass


class HsHierarchyElement(HsWrapper):
    """
    Base class for wrapped Haskell elements with a hierarchical structure.

    Provides a common base class for treating immutable Haskell objects as mutable Python objects with a hierarchical structure.
    """
    def __init__(self, parent: Optional):
        super().__init__()

        self._parent = parent

    def parent(self) -> Optional:
        """
        Get the parent of the element if the element is not the root.
        :return: The parent element
        """
        return self._parent

    def root(self):
        """
        Get the root element of the hierarchy.
        :return: Root element
        """
        if self.parent() is None:
            return self

        return self.parent().root()



