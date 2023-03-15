from typing import Generic, TypeVar, Optional


class HsWrapper:
    def hsObj(self):
        pass

    def hsUpdate(self, newHsObj):
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



