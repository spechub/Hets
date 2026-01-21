from gi.repository import Gtk

from ..GtkSmartTemplate import GtkSmartTemplate
from hets import Sentence, Theory
from ..widgets import ProofDetail


@GtkSmartTemplate
class ProofDetailsWindow(Gtk.Window):
    __gtype_name__ = "ProofDetailsWindow"

    _box_proof_details: Gtk.Box = Gtk.Template.Child()

    def __init__(self, goal: Sentence, theory: Theory, **kwargs):
        super().__init__(**kwargs)
        self.maximize()
        self.set_title(f"Proof details for {goal.name()}")

        self.goal = goal
        self.theory = theory

        for comorphism, proof in goal.theorem_status():
            proof_detail = ProofDetail()
            proof_detail.proof = proof
            proof_detail.comorphism = comorphism
            proof_detail.theory = theory

            self._box_proof_details.pack_start(proof_detail, False, True, 4)

        self.show_all()
