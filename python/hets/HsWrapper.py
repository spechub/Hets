"""
Description :  Defines a common base class for wrapped haskell elements
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
"""

from typing import Generic, TypeVar, Optional


class HsWrapper:
    def hs_obj(self):
        pass

    def hs_update(self, new_hs_obj):
        pass


class HsHierarchyElement(HsWrapper):
    def __init__(self, parent: Optional):
        super().__init__()

        self._parent = parent

    def parent(self) -> Optional:
        return self._parent

    def root(self):
        if self.parent() is None:
            return self

        return self.parent().root()



