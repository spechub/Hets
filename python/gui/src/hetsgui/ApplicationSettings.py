from collections.abc import Callable
from dataclasses import dataclass
from typing import Optional, Any

from gi.repository.GLib import KeyFile


class ApplicationSettings:
    """
    Class to store application settings with a KeyFile (.ini).
    """

    keyfile: KeyFile

    def __init__(self, keyfile: KeyFile):
        self.keyfile = keyfile

    def _get(self, m: Callable[[str, str], Any], group_name: str, key: str) -> Optional[Any]:
        """
        Helper function to get an optional value from the keyfile.

        :param m: function on `KeyFile`
        :param group_name: passed to m
        :param key: passed to m
        :return:
        """
        try:
            return m(group_name, key)
        except:
            return None


    @property
    def apply_proof_rules_automatically(self) -> Optional[bool]:
        """
        Whether automatic proof rules should be applied automatically when loading a library.
        :return: None if not set, otherwise the value
        """

        return self._get(self.keyfile.get_boolean, "hets", "apply_proof_rules_automatically")

    @apply_proof_rules_automatically.setter
    def apply_proof_rules_automatically(self, value: bool) -> None:
        self.keyfile.set_boolean("hets", "apply_proof_rules_automatically", value)

