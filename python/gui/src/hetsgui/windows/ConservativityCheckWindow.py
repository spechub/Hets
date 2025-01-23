import logging
import threading
import traceback
import typing
from threading import Thread

from gi.repository import Gtk, GLib

from hets import DevGraphEdge, ConservativityChecker, ConsistencyKind
from ..GtkSmartTemplate import GtkSmartTemplate


@GtkSmartTemplate
class ConservativityCheckWindow(Gtk.Window):
    """
    A window to check the conservativity of a DevGraphEdge.
    """
    _edge: DevGraphEdge
    _checking_thread: typing.Optional[Thread]

    __gtype_name__ = 'ConservativityCheckWindow'
    _logger = logging.getLogger(__name__)

    # UI elements
    _btn_check: Gtk.Button = Gtk.Template.Child()
    _combo_checker: Gtk.ComboBox = Gtk.Template.Child()
    _lbl_status: Gtk.Label = Gtk.Template.Child()
    _lbl_output: Gtk.Label = Gtk.Template.Child()

    # Models
    _checker_model: Gtk.ListStore = Gtk.Template.Child()

    @property
    def selected_conservativity_checker(self) -> typing.Optional[ConservativityChecker]:
        """
        The selected conservativity checker or None if no checker is selected.
        :return: 
        """
        active_index = self._combo_checker.get_active()
        cc_name = self._checker_model[active_index][0] if active_index >= 0 else None
        cc = self._edge.get_conservativity_checker_by_name(cc_name) if cc_name else None
        return cc

    def __init__(self, edge: DevGraphEdge, **kwargs):
        super().__init__(title=f"Check conservativity of {edge.title()}", **kwargs)

        self._checking_thread = None
        self._edge = edge

        self._update_status(edge.conservativity())

        # Build conservativity checkers model
        ccs = self._edge.get_usable_conservativity_checkers()
        for cc in ccs:
            self._checker_model.append([cc.name(), cc.name(), 0])

        if len(self._checker_model) > 0:
            self._combo_checker.set_active(0)

    @Gtk.Template.Callback()
    def on_check_clicked(self, *args):
        """
        Called when the user clicks the check button. Starts the conservativity check in a separate background thread.
        :param args: ignored
        :return:
        """

        if self._checking_thread is not None and self._checking_thread.is_alive():
            self._logger.warning("Conservativity check is already running. Waiting for it to finish.")
            self._checking_thread.join()

        self._checking_thread = threading.Thread(target=self._check_consistency)
        self._checking_thread.start()

    def _update_status(self, status: typing.Union[ConsistencyKind, str]):
        """
        Update the status label with the given status.
        :param status: The status to display.
        :return:
        """

        # Remove the previous status class
        style_context = self._lbl_status.get_style_context()
        style_context.remove_class("consistency-kind-inconsistent")
        style_context.remove_class("consistency-kind-unknown")
        style_context.remove_class("consistency-kind-pcons")
        style_context.remove_class("consistency-kind-cons")
        style_context.remove_class("consistency-kind-mono")
        style_context.remove_class("consistency-kind-defined")
        style_context.remove_class("consistency-kind-timed_out")
        style_context.remove_class("consistency-kind-error")

        if isinstance(status, ConsistencyKind):
            # Add the new status class
            style_context.add_class(f"consistency-kind-{status.name.lower()}")
            self._lbl_status.set_markup(f'<b>{status.to_str()}</b>')
        else:
            self._lbl_status.set_markup(status)

    def _check_consistency(self):
        """
        Check the conservativity of the edge.

        This function is blocking and is designed to be run in a background thread.
        :return:
        """

        edge = self._edge

        # Update the UI in the main thread
        GLib.idle_add(self._init_checking_progress)

        try:
            conservativity_checker = self.selected_conservativity_checker

            self._logger.info("Checking conservativity on %s, checker: %s", edge.title(),
                              conservativity_checker.name())

            status, explanations, obligations, diagnosis = edge.check_conservativity(conservativity_checker)

            self._logger.info("Conservativity check result for %s: %s", edge.title(), status)

            if status is None:
                status = ConsistencyKind.UNKNOWN
                message = "\n".join(diagnosis)
            else:
                if explanations:
                    self._logger.debug("Conservativity check explained by sentences: %s", edge.title(),
                                       ", ".join(explanations))
                if obligations:
                    self._logger.debug("Conservativity check has open proof obligations: %s", edge.title(),
                                       ", ".join(obligations))

                # Build a message for the user
                message = f"The link is {status.to_str()}"
                if obligations:
                    message += " provided that the following obligations hold in an imported theory:\n"
                    message += ", ".join(obligations)
                elif explanations:
                    message += " because of the following axioms:\n"
                    message += ", ".join(explanations)

                message += "\n" + "\n".join(diagnosis)
        except BaseException as e:
            self._logger.warning("Conservativity check for %s failed: %s", edge.title(), traceback.format_exc())

            status = ConsistencyKind.ERROR
            message = str(e)

        # Update the UI in the main thread
        GLib.idle_add(self._finish_checking_progress, status, message)

    def _finish_checking_progress(self, status: ConsistencyKind, message: str):
        """
        Called when the consistency check has finished. Updates the UI accordingly.
        :param status: The resulting status of the check.
        :param message: The message to display.
        :return:
        """

        self._btn_check.set_sensitive(True)
        self._update_status(status)

        message = message.strip()
        if len(message) > 0:
            self._lbl_output.set_lines(len(message.split("\n")))
            self._lbl_output.set_text(message)
            self._lbl_output.set_halign(Gtk.Align.START)
        else:
            self._lbl_output.set_lines(1)
            self._lbl_output.set_markup("<i>No output</i>")
            self._lbl_output.set_halign(Gtk.Align.CENTER)

    def _init_checking_progress(self):
        """
        Called when the consistency check starts. Updates the UI accordingly.
        :return:
        """

        self._btn_check.set_sensitive(False)
        self._update_status("<i>Checking</i>")
