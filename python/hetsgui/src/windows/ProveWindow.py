import threading
from typing import Optional

from gi.repository import Gtk, GLib

from GtkSmartTemplate import GtkSmartTemplate
from hets import DevGraphNode, ProofKind, Comorphism, Prover, Sentence
from formatting.Colors import PROOF_KIND_BG_COLORS, color_name_to_rgba
from windows.ProofDetailsWindow import ProofDetailsWindow

from widgets import CellRendererLink, GridWithToolComorphismSelector


@GtkSmartTemplate
class ProveWindow(Gtk.Window):
    __gtype_name__ = "ProveWindow"

    goals_model: Gtk.ListStore = Gtk.Template.Child()
    axioms_model: Gtk.ListStore = Gtk.Template.Child()

    notebook: Gtk.Notebook = Gtk.Template.Child()
    btn_prove: Gtk.Button = Gtk.Template.Child()
    txt_extra_options: Gtk.Entry = Gtk.Template.Child()
    txt_timeout: Gtk.SpinButton = Gtk.Template.Child()
    switch_include_proven_theorems: Gtk.Switch = Gtk.Template.Child()

    _lbl_sublogic: Gtk.Label = Gtk.Template.Child()
    _prover_comorphism_selector: GridWithToolComorphismSelector = Gtk.Template.Child()

    @property
    def selected_comorphism(self) -> Comorphism:
        return self._prover_comorphism_selector.selected_comorphism

    @property
    def selected_prover(self) -> Prover:
        return self._prover_comorphism_selector.selected_prover

    def __init__(self, node: DevGraphNode, **kwargs):
        super().__init__(title=f"Prove {node.name()}", **kwargs)

        self.proving_thread: Optional[threading.Thread] = None
        self.node = node
        self._prover_comorphism_selector.theory = node.global_theory()
        self._init_view()

        self.update_sublogic()

    def _init_view(self):

        # Add goals to goals model for display in tree view
        for goal in self.node.global_theory().goals():
            color, text = self._goal_style(goal)

            self.goals_model.append(
                [goal.name(), True, text, goal.name(), str(goal), color])

        # Add axioms to axioms model for display in tree view
        for axiom in self.node.global_theory().axioms():
            self.axioms_model.append(
                [axiom.name(), True, axiom.name(), str(axiom)])

    def _goal_style(self, g: Sentence):
        proof = g.best_proof()
        kind = proof.kind() if proof is not None else ProofKind.OPEN
        goal_text = f'<span foreground="black" underline="single">{kind.to_str()}</span>'
        color_name = PROOF_KIND_BG_COLORS[kind]
        goal_color = color_name_to_rgba(color_name)
        return goal_color, goal_text

    @Gtk.Template.Callback()
    def on_close(self, widget, event):
        if self.proving_thread is not None and self.proving_thread.is_alive():
            return True  # Stop the window from being closed if a proving process is currently running

        return False

    @Gtk.Template.Callback()
    def on_prove_clicked(self, _):
        self.proving_thread = threading.Thread(target=self._prove)
        # self.proving_thread.daemon = True
        self.proving_thread.start()

    @Gtk.Template.Callback()
    def on_proof_details_clicked(self, widget, path):
        goal_name = self.goals_model[path][0]
        goal = next(iter(g for g in self.node.global_theory().goals()
                    if g.name() == goal_name), None)

        if goal is not None:
            details_window = ProofDetailsWindow(
                goal, self.node.global_theory())
            details_window.show_all()
            details_window.present()

    @Gtk.Template.Callback()
    def on_goals_changed(self, model: Gtk.ListStore, path: Gtk.TreePath, it: Gtk.TreeIter):
        self.update_sublogic()

    @Gtk.Template.Callback()
    def on_axioms_changed(self, model: Gtk.ListStore, path: Gtk.TreePath, it: Gtk.TreeIter):
        self.update_sublogic()

    def _init_prove_progress(self):
        self.btn_prove.set_sensitive(False)
        self.notebook.set_current_page(1)

        for goal in self.goals_model:
            if goal[1]:  # if selected to be proven
                goal[2] = '<span foreground="black" style="italic">Waiting...</span>'
                color = color_name_to_rgba("white")
                goal[5] = color
        
    def _update_prove_progress(self, next_goal_name: Optional[str], prev_goal_name: Optional[str]):
        if prev_goal_name is not None:
            goal_row = next(
                iter(g for g in self.goals_model if g[0] == prev_goal_name), None)
            goal = next(iter(g for g in self.node.global_theory(
            ).goals() if g.name() == prev_goal_name), None)

            if goal_row is not None:
                color, text = self._goal_style(goal)
                goal_row[2] = text
                goal_row[5] = color

        if next_goal_name is not None:
            goal_row = next(
                iter(g for g in self.goals_model if g[0] == next_goal_name), None)
            if goal_row is not None:
                goal_row[2] = '<span foreground="black" style="italic">Proving...</span>'

    def _finish_prove_progress(self):
        self.btn_prove.set_sensitive(True)
        self.notebook.set_current_page(1)

    def _prove(self):
        GLib.idle_add(self._init_prove_progress)

        goals = [row[0] for row in self.goals_model if row[1]]
        axioms = [row[0] for row in self.axioms_model if row[1]]

        prover = self.selected_prover
        comorphism = self.selected_comorphism
        timeout = self.txt_timeout.get_value_as_int()
        include_theorems = self.switch_include_proven_theorems.get_active()

        prev_goal = None
        for i, goal in enumerate(goals):
            GLib.idle_add(self._update_prove_progress, goal, prev_goal)

            self.node.prove(prover, comorphism, include_theorems, [
                            goal], axioms, timeout)
            prev_goal = goal

        GLib.idle_add(self._update_prove_progress, None, prev_goal)

        GLib.idle_add(self._finish_prove_progress)

    def update_sublogic(self):
        if self.proving_thread is None or not self.proving_thread.is_alive():

            axioms = [row[0] for row in self.axioms_model if row[1]]
            goals = [row[0] for row in self.goals_model if row[1]]

            sub_logic = self.node.global_theory().with_selection(axioms, goals).get_sublogic()
            self._lbl_sublogic.set_label(sub_logic)
