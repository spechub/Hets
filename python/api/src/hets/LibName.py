from typing import Optional

from .haskell import LibName as HsLibName, libVersion, getLibId, mimeType, getFilePath, show

from .maybe import maybe_to_optional
from .Pretty import Pretty


class LibName:
    def __init__(self, hs_libname: HsLibName):
        self._hs_libname = hs_libname

    def version(self) -> Optional[str]:
        """
        Returns the version of the library, if available

        :return: version of the library, if available
        """

        return maybe_to_optional(libVersion(self._hs_libname))

    def id(self) -> Pretty[object]:
        """
        Returns a unique identifier of the library.

        :return: Unique identifier of the library
        """

        return Pretty(getLibId(self._hs_libname))

    def location(self) -> Optional[str]:
        """
        Returns the physical location i.e. file path of the library, if available

        :return: Physical location, if available
        """
        path = getFilePath(self._hs_libname)

        return None if path == "" else path

    def mime_type(self) -> Optional[str]:
        """
        Returns the mime type of the library, if available

        :return: mime type of the library, if available
        """

        return maybe_to_optional(mimeType(self._hs_libname))

    def __eq__(self, other):
        return isinstance(other, LibName) and other.id() == self.id()

    def __hash__(self):
        return hash(self.id())

    def __str__(self):
        return show(self._hs_libname)
