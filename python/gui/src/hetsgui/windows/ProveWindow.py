import concurrent.futures
import logging
import threading
import traceback
from threading import Thread
from typing import Optional, Tuple

from gi.repository import Gtk, GLib, Gdk

from hets import DevGraphNode, ProofKind, Comorphism, Prover, Sentence
from ..GtkSmartTemplate import GtkSmartTemplate
from ..formatting.colors import PROOF_KIND_BG_COLORS, color_name_to_rgba
from ..widgets import GridWithToolComorphismSelector
from ..windows.ProofDetailsWindow import ProofDetailsWindow


@GtkSmartTemplate
class ProveWindow(Gtk.Window):
    """
    A window to prove goals at a DevGraphNode.
    """

    __gtype_name__ = "ProveWindow"
    _logger = logging.getLogger(__name__)
    _prove_lock: threading.Lock
    _proving_thread: Optional[Thread]

    _node: DevGraphNode

    # Models
    _goals_model: Gtk.ListStore = Gtk.Template.Child()
    _axioms_model: Gtk.ListStore = Gtk.Template.Child()

    # UI elements
    _notebook: Gtk.Notebook = Gtk.Template.Child()
    _btn_prove: Gtk.Button = Gtk.Template.Child()
    _txt_extra_options: Gtk.Entry = Gtk.Template.Child()
    _txt_timeout: Gtk.SpinButton = Gtk.Template.Child()
    _switch_include_proven_theorems: Gtk.Switch = Gtk.Template.Child()

    _lbl_sublogic: Gtk.Label = Gtk.Template.Child()
    _prover_comorphism_selector: GridWithToolComorphismSelector = Gtk.Template.Child()

    @property
    def selected_comorphism(self) -> Optional[Comorphism]:
        """
        The selected comorphism or None if no comorphism is selected.
        :return:
        """
        return self._prover_comorphism_selector.selected_comorphism

    @property
    def selected_prover(self) -> Optional[Prover]:
        """
        The selected prover or None if no prover is selected.
        :return:
        """
        return self._prover_comorphism_selector.selected_prover

    def __init__(self, node: DevGraphNode, **kwargs):
        super().__init__(title=f"Prove {node.name()}", **kwargs)

        self._proving_thread: Optional[threading.Thread] = None
        self._prove_lock = threading.Lock()
        self._node = node
        self._prover_comorphism_selector.theory = node.global_theory()
        self._init_view()

        self.update_sublogic()

    def _init_view(self):
        """
        Add goals and axioms to the models.
        :return:
        """

        # Add goals to goals model for display in tree view
        for goal in self._node.global_theory().goals():
            color, text = self._goal_style(goal)

            self._goals_model.append(
                [goal.name(), True, text, goal.name(), str(goal), color])

        # Add axioms to axioms model for display in tree view
        for axiom in self._node.global_theory().axioms():
            self._axioms_model.append(
                [axiom.name(), True, axiom.name(), str(axiom)])

    def _goal_style(self, g: Sentence) -> Tuple[Gdk.RGBA, str]:
        """
        Get the style for a goal.
        :param g: The goal.
        :return: The color and text for the goal.
        """
        proof = g.best_proof()
        kind = proof.kind() if proof is not None else ProofKind.OPEN
        goal_text = f'<span foreground="black" underline="single">{kind.to_str()}</span>'
        color_name = PROOF_KIND_BG_COLORS[kind]
        goal_color = color_name_to_rgba(color_name)
        return goal_color, goal_text

    @Gtk.Template.Callback()
    def on_close(self, widget, event):
        """
        Called when the window is closed. Prevents the window from being closed if a proving process is currently running.
        :param widget: ignored
        :param event: ignored
        :return:
        """
        if self._proving_thread is not None and self._proving_thread.is_alive():
            return True  # Stop the window from being closed if a proving process is currently running

        return False

    @Gtk.Template.Callback()
    def on_prove_clicked(self, _):
        """
        Called when the user clicks the prove button. Starts the proving process in a separate background thread.
        :param _: ignored
        :return:
        """
        self._proving_thread = threading.Thread(target=self._prove)
        self._proving_thread.start()

    @Gtk.Template.Callback()
    def on_proof_details_clicked(self, widget, path):
        """
        Called when the user clicks the proof details button. Shows the proof details for the selected goal.
        :param widget: ignored
        :param path: The path of the selected goal.
        :return:
        """
        goal_name = self._goals_model[path][0]
        goal = next(iter(g for g in self._node.global_theory().goals()
                         if g.name() == goal_name), None)

        if goal is not None:
            details_window = ProofDetailsWindow(goal, self._node.global_theory())
            details_window.show_all()
            details_window.present()

    @Gtk.Template.Callback()
    def on_goals_changed(self, model: Gtk.ListStore, path: Gtk.TreePath, it: Gtk.TreeIter):
        self.update_sublogic()

    @Gtk.Template.Callback()
    def on_axioms_changed(self, model: Gtk.ListStore, path: Gtk.TreePath, it: Gtk.TreeIter):
        self.update_sublogic()

    def _init_prove_progress(self):
        """
        Called when the proving process is started. Updates the UI accordingly.
        :return:
        """
        self._btn_prove.set_sensitive(False)
        self._notebook.set_current_page(0)

        for goal in self._goals_model:
            if goal[1]:  # if selected to be proven
                goal[2] = '<span foreground="black" style="italic">Waiting...</span>'
                color = color_name_to_rgba("white")
                goal[5] = color

    def _finish_prove_progress_goal(self, goal_name: str):
        """
        Called when a goal has been proven. Updates the UI accordingly.
        :param goal_name: The proven goal
        :return:
        """

        goal_row = next(iter(g for g in self._goals_model if g[0] == goal_name), None)
        goal = next(iter(g for g in self._node.global_theory().goals() if g.name() == goal_name), None)

        if goal_row is not None:
            color, text = self._goal_style(goal)
            goal_row[2] = text
            goal_row[5] = color

    def _start_prove_progress_goal(self, goal_name: str):
        """
        Called when a goal is being proven. Updates the UI accordingly.
        :param goal_name: The goal being proven
        :return:
        """
        goal_row = next(
            iter(g for g in self._goals_model if g[0] == goal_name), None)
        if goal_row is not None:
            goal_row[2] = '<span foreground="black" style="italic">Proving...</span>'

    def _finish_prove_progress(self):
        """
        Called when the proving process has finished. Updates the UI accordingly.
        :return:
        """
        self._btn_prove.set_sensitive(True)
        self._notebook.set_current_page(0)

    def _prove(self):
        """
        Proves the selected goals at the node. The function is blocking and designed to be run in a separate background thread.
        :return:
        """

        # Update the UI in the main thread
        GLib.idle_add(self._init_prove_progress)

        goals = [row[0] for row in self._goals_model if row[1]]
        axioms = [row[0] for row in self._axioms_model if row[1]]

        prover = self.selected_prover
        comorphism = self.selected_comorphism
        timeout = self._txt_timeout.get_value_as_int()
        include_theorems = self._switch_include_proven_theorems.get_active()

        def prove_goal(g):
            GLib.idle_add(self._start_prove_progress_goal, g)

            self._logger.debug("Proving at node %s. Next goal: %s", self._node.name(), g)
            try:
                self._node.prove(prover, comorphism, include_theorems, [g], axioms, timeout)
            except Exception as e:
                self._logger.warning("Proving at node %s failed for goal %s: %s", self._node.name(), g,
                                     traceback.format_exc())

                dialog = Gtk.MessageDialog(transient_for=self, flags=0, message_type=Gtk.MessageType.ERROR,
                                           buttons=Gtk.ButtonsType.CLOSE, text=f"Proving failed!")
                dialog.format_secondary_text(f"Check the console for more details. Error message: {str(e)}")
                dialog.run()
                dialog.destroy()

            GLib.idle_add(self._finish_prove_progress_goal, g)

        self._logger.info(
            "Proving at node %s, goals: %s, axioms: %s, prover: %s, comorphism: %s, timeout: %s, include_theorems: %s",
            self._node.name(), goals, axioms, prover.name(), comorphism.name(), timeout, include_theorems)

        # Prove the goals in parallel if previously proven goals should be included in subsequent proofs, otherwise prove them sequentially
        if include_theorems:
            self._logger.debug("Theorems included. Proving sequentially")
            for goal in goals:
                prove_goal(goal)
        else:
            self._logger.debug("Theorems not included. Proving in parallel")
            with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
                concurrent.futures.wait([executor.submit(prove_goal, goal) for goal in goals])

        # Update the UI in the main thread
        GLib.idle_add(self._finish_prove_progress)

    def update_sublogic(self):
        """
        Updates the label for the sublogic when the selection of axioms and goals changes.
        :return:
        """
        if self._proving_thread is None or not self._proving_thread.is_alive():
            axioms = [row[0] for row in self._axioms_model if row[1]]
            goals = [row[0] for row in self._goals_model if row[1]]

            sub_logic = self._node.global_theory().with_selection(axioms, goals).get_sublogic()
            self._lbl_sublogic.set_label(sub_logic)
