import logging
import threading
import traceback
import typing

from gi.repository import Gtk, GLib

from ..GtkSmartTemplate import GtkSmartTemplate
from hets import DevGraphNode, ConsistencyChecker, Comorphism, ConsistencyKind
from ..widgets import GridWithToolComorphismSelector


@GtkSmartTemplate
class ConsistencyCheckWindow(Gtk.Window):
    __gtype_name__ = 'ConsistencyCheckWindow'
    _logger = logging.getLogger(__name__)

    _consistency_checker_comorphism_selector: GridWithToolComorphismSelector = Gtk.Template.Child()
    _btn_check: Gtk.Button = Gtk.Template.Child()

    _switch_include_proven_theorems: Gtk.Switch = Gtk.Template.Child()
    _txt_timeout: Gtk.SpinButton = Gtk.Template.Child()
    _lbl_status: Gtk.Label = Gtk.Template.Child()
    _lbl_output: Gtk.Label = Gtk.Template.Child()

    @property
    def selected_comorphism(self) -> typing.Optional[Comorphism]:
        return self._consistency_checker_comorphism_selector.selected_comorphism

    @property
    def selected_consistency_checker(self) -> ConsistencyChecker:
        return self._consistency_checker_comorphism_selector.selected_consistency_checker

    def __init__(self, node: DevGraphNode, **kwargs):
        super().__init__(title=f"Check consistency of {node.name()}", **kwargs)

        self.checking_thread = None
        self._consistency_checker_comorphism_selector.theory = node.global_theory()
        self._node = node

        self._update_status(node.consistency_status().proven())

    @Gtk.Template.Callback()
    def on_check_clicked(self, *args):
        self.checking_thread = threading.Thread(target=self._check_consistency)
        # self.proving_thread.daemon = True
        self.checking_thread.start()

    def _update_status(self, status: typing.Union[ConsistencyKind, str]):
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
            style_context.add_class(f"consistency-kind-{status.name.lower()}")
            self._lbl_status.set_markup(f'<b>{status.to_str()}</b>')
        else:
            self._lbl_status.set_markup(status)

    def _check_consistency(self):
        GLib.idle_add(self._init_checking_progress)

        try:
            consistency_checker = self.selected_consistency_checker
            comorphism = self.selected_comorphism
            timeout = self._txt_timeout.get_value_as_int()
            include_theorems = self._switch_include_proven_theorems.get_active()

            self._logger.info(
                "Checking consistency on %s, checker: %s, comorphism: %s, timeout: %s, include_theorems: %s",
                self._node.name(), consistency_checker.name(), comorphism.name(), timeout, include_theorems)

            status, message = self._node.check_consistency(consistency_checker, comorphism, include_theorems, timeout)

            self._logger.info("Consistency result for %s: %s", self._node.name(), status)
            self._logger.debug("Consistency check message for %s: %s", self._node.name(), message)
        except Exception as e:
            self._logger.warning("Consistency check for %s failed: %s", self._node.name(), traceback.format_exc())

            dialog = Gtk.MessageDialog(transient_for=self, flags=0, message_type=Gtk.MessageType.ERROR,
                                       buttons=Gtk.ButtonsType.CLOSE, text=f"Check failed!")
            dialog.format_secondary_text(f"Check the console for more details.\nError message: {str(e)}")
            dialog.run()
            dialog.destroy()

            status = ConsistencyKind.ERROR
            message = str(e)

        GLib.idle_add(self._finish_checking_progress, status, message)

    def _finish_checking_progress(self, status: ConsistencyKind, message: str):
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
        self._btn_check.set_sensitive(False)
        self._update_status("<i>Checking</i>")
