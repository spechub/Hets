import re
import typing

from gi.repository import Gtk, GObject, Gio

from GtkSmartTemplate import GtkSmartTemplate
from formatting.colors import PROOF_KIND_FG_COLORS
from widgets import ExtendedDotWidget


class AxiomModel(GObject.GObject):
    def __init__(self, name: str, sentence: typing.Optional[str]):
        GObject.GObject.__init__(self)
        self.name = name
        self.sentence = sentence


@GtkSmartTemplate
class ProofDetail(Gtk.Bin):
    __gtype_name__ = "ProofDetail"

    proof = GObject.Property(type=object)
    comorphism = GObject.Property(type=object)
    theory = GObject.Property(type=object)

    _lbl_title: Gtk.Label = Gtk.Template.Child()
    _lbl_prover: Gtk.Label = Gtk.Template.Child()
    _lbl_comorphism: Gtk.Label = Gtk.Template.Child()
    _lbl_used_time: Gtk.Label = Gtk.Template.Child()
    _lbl_status: Gtk.Label = Gtk.Template.Child()
    _lbl_proof_lines: Gtk.Label = Gtk.Template.Child()

    _dot_proof_tree: ExtendedDotWidget = Gtk.Template.Child()

    _lbl_ts_time: Gtk.Label = Gtk.Template.Child()
    _lbl_ts_time_value: Gtk.Label = Gtk.Template.Child()
    _lbl_ts_opts: Gtk.Label = Gtk.Template.Child()
    _lbl_ts_opts_value: Gtk.Label = Gtk.Template.Child()
    _lbl_ts: Gtk.Label = Gtk.Template.Child()
    _lbl_ts_value: Gtk.Label = Gtk.Template.Child()

    _box_axioms: Gtk.FlowBox = Gtk.Template.Child()

    _model_axioms: Gio.ListStore

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        self._model_axioms = Gio.ListStore.new(AxiomModel)

        self.connect("notify::comorphism", self.on_comorphism_changed)
        self.connect("notify::proof", self.on_proof_changed)
        self.connect("notify::theory", self.update_axioms)

        self._box_axioms.bind_model(self._model_axioms, self.create_axiom_widget)

    def create_axiom_widget(self, item, *args):
        label = Gtk.Label(label=item.name, tooltip_text=str(item.sentence) if item.sentence else item.name)
        label.get_style_context().add_class("axiom")
        return label

    def on_proof_changed(self, widget, param):
        self._lbl_prover.set_label(self.proof.details().used_prover())
        self._lbl_prover.set_tooltip_text(self.proof.details().used_prover())
        self._lbl_status.set_markup(
            f"<span foreground='{PROOF_KIND_FG_COLORS[self.proof.kind()]}'>{self.proof.kind().to_str()}</span>")
        self._lbl_used_time.set_label(str(self.proof.details().used_time()))

        proof_lines = self.proof.details().proof_lines()
        self._lbl_proof_lines.set_text("\n".join(proof_lines))
        self._lbl_proof_lines.set_lines(len(proof_lines))

        self._dot_proof_tree.dotcode = self.proof.details().proof_tree()

        self.update_tactic_script()
        self.update_axioms()
        self.update_title()

    def on_comorphism_changed(self, widget, param):
        self._lbl_comorphism.set_label(self.comorphism.name())
        self._lbl_comorphism.set_tooltip_text(self.comorphism.name())

        self.update_title()

    def update_title(self):
        if not (self.comorphism and self.proof):
            return

        color = PROOF_KIND_FG_COLORS[self.proof.kind()]

        self._lbl_title.set_markup(
            f"<span foreground='{color}'>{self.proof.kind().to_str()}</span> with <b>{self.proof.details().used_prover()}</b> via <b>{self.comorphism.name()}</b>")

    def update_axioms(self, *args):
        if not (self.proof and self.theory):
            return

        self._model_axioms.remove_all()
        for axiom in self.proof.details().used_axioms():
            sentence = self.theory.sentence_by_name(axiom)
            self._model_axioms.append(AxiomModel(axiom, sentence))

    def update_tactic_script(self):
        ts_regex = [
            re.compile(r"^ATPTacticScript \{tsTimeLimit = (\d+), tsExtraOpts = \[(.*)\]\}$"),
            re.compile(r"^TacticScript \{timeLimit = (\d+), extraOptions = \[(.*)\]\}$")
        ]
        ts_time, ts_opts = None, None

        tactic_script = self.proof.details().tactic_script()
        for regex in ts_regex:
            match = regex.match(tactic_script)
            if match:
                ts_time = match.group(1)
                ts_opts_list = match.group(2)
                list_regex = re.compile(r"\"((?:\\\"|[^\"])*)\"")
                ts_opts = []
                for match in list_regex.finditer(ts_opts_list):
                    ts_opts.append(match.group(1))

                ts_opts = " ".join(ts_opts)

                break

        if ts_time is None and ts_opts is None:
            self._lbl_ts_time.set_visible(False)
            self._lbl_ts_time_value.set_visible(False)
            self._lbl_ts_opts.set_visible(False)
            self._lbl_ts_opts_value.set_visible(False)
            self._lbl_ts.set_visible(True)
            self._lbl_ts_value.set_visible(True)

            self._lbl_ts_value.set_label(tactic_script)

        else:
            self._lbl_ts_time.set_visible(True)
            self._lbl_ts_time_value.set_visible(True)
            self._lbl_ts_opts.set_visible(True)
            self._lbl_ts_opts_value.set_visible(True)
            self._lbl_ts.set_visible(False)
            self._lbl_ts_value.set_visible(False)

            self._lbl_ts_time_value.set_label(f"{ts_time}s")
            self._lbl_ts_opts_value.set_label(ts_opts)
