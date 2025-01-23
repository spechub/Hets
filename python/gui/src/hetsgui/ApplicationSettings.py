from collections.abc import Callable
from dataclasses import dataclass
from typing import Optional, Any

from gi.repository.GLib import KeyFile


class ApplicationSettings:
    keyfile: KeyFile

    def __init__(self, keyfile: KeyFile):
        self.keyfile = keyfile

    def _get(self, m: Callable[[str, str], Any], group_name: str, key: str) -> Optional[Any]:
        try:
            return m(group_name, key)
        except:
            return None


    @property
    def apply_proof_rules_automatically(self) -> Optional[bool]:
        return self._get(self.keyfile.get_boolean, "hets", "apply_proof_rules_automatically")

    @apply_proof_rules_automatically.setter
    def apply_proof_rules_automatically(self, value: bool) -> None:
        self.keyfile.set_boolean("hets", "apply_proof_rules_automatically", value)

