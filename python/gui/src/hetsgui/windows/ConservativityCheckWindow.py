import logging
import threading
import traceback
import typing

from gi.repository import Gtk, GLib

from ..GtkSmartTemplate import GtkSmartTemplate
from hets import DevGraphEdge, ConsistencyChecker, ConservativityChecker, ConsistencyKind, TheoremDevGraphEdge
from ..widgets import GridWithToolComorphismSelector


@GtkSmartTemplate
class ConservativityCheckWindow(Gtk.Window):
    __gtype_name__ = 'ConservativityCheckWindow'
    _logger = logging.getLogger(__name__)

    _btn_check: Gtk.Button = Gtk.Template.Child()

    _checker_model: Gtk.ListStore = Gtk.Template.Child()
    _combo_checker: Gtk.ComboBox = Gtk.Template.Child()
    _lbl_status: Gtk.Label = Gtk.Template.Child()
    _lbl_output: Gtk.Label = Gtk.Template.Child()

    @property
    def selected_conservativity_checker(self) -> typing.Optional[ConservativityChecker]:
        active_index = self._combo_checker.get_active()
        cc_name = self._checker_model[active_index][0] if active_index >= 0 else None
        cc = self._edge.get_conservativity_checker_by_name(cc_name) if cc_name else None
        return cc

    def __init__(self, edge: DevGraphEdge, **kwargs):
        super().__init__(title=f"Check conservativity of {edge.name()}", **kwargs)

        self.checking_thread = None
        self._edge = edge

        self._update_status(edge.conservativity())

        ccs = self._edge.get_usable_conservativity_checkers()
        for cc in ccs:
            self._checker_model.append([cc.name(), cc.name(), 0])

        if len(self._checker_model) > 0:
            self._combo_checker.set_active(0)

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
        edge = self._edge
        if not isinstance(edge, TheoremDevGraphEdge):
            self._logger.warning(f"Edge '{edge.name()}' is not a theorem edge. Conservativity cannot be computed.")

            return

        GLib.idle_add(self._init_checking_progress)

        try:
            conservativity_checker = self.selected_conservativity_checker

            self._logger.info("Checking conservativity on %s, checker: %s", self._edge.name(),
                              conservativity_checker.name())

            status, explanations, obligations = edge.check_conservativity(conservativity_checker)

            self._logger.info("Conservativity check result for %s: %s", self._edge.name(), status)
            self._logger.debug("Conservativity check explained by sentences: %s", self._edge.name(), ", ".join(explanations))
            self._logger.debug("Conservativity check has open proof obligations: %s", self._edge.name(), ", ".join(obligations))

            message = f"The link is {status.to_str()}"
            if obligations:
                message += " provided that the following obligations hold in an imported theory:\n"
                message += ", ".join(str(s) for s in obligations)
            elif explanations:
                message += " because of the following axioms:\n"
                message += ", ".join(str(s) for s in explanations)

        except Exception as e:
            self._logger.warning("Conservativity check for %s failed: %s", self._edge.name(), traceback.format_exc())

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
