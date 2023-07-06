import re

import xdot.dot.lexer
from gi.repository import Gtk, Pango

from formatting.Colors import PROOF_KIND_BG_COLORS, PROOF_KIND_FG_COLORS
from hets import Sentence, Theory

from graphviz import Graph, Digraph
from xdot import DotWidget
import time


class ProofDetailsWindow(Gtk.Window):
    def __init__(self, goal: Sentence, theory: Theory, **kwargs):
        super().__init__(**kwargs)

        provider = Gtk.CssProvider()
        provider.load_from_data(b"""
        .axiom { background: #00BBFF; }
        .proof-tree { background: white; }
        .proof-lines { font-family: monospace; }
        """)
        # self.get_style_context().add_provider(provider, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)
        self.get_style_context().add_provider_for_screen(self.get_screen(), provider, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)

        self.goal = goal
        self.theory = theory

        self.set_default_size(800, 600)
        self.maximize()
        self.set_title(f"Proof details for {goal.name()}")

        # self.header = Gtk.HeaderBar(title=self.get_title())
        # self.set_titlebar(self.header)

        self.scrolled_window = Gtk.ScrolledWindow(hexpand=True, vexpand=True, hscrollbar_policy=Gtk.PolicyType.NEVER)
        self.add(self.scrolled_window)

        self.box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        self.scrolled_window.add(self.box)

        for comorphism, proof in goal.theorem_status():
            expander = Gtk.Expander()
            expander_label = Gtk.Label()
            expander_label.set_tooltip_text(f"{proof.kind().to_str()} with {proof.details().used_prover()} via {comorphism.name()}")
            expander_label.set_markup(f"<span foreground='{PROOF_KIND_FG_COLORS[proof.kind()]}'>{proof.kind().to_str()}</span> with <b>{proof.details().used_prover()}</b> via <b>{comorphism.name()}</b>")
            expander_label.set_ellipsize(Pango.EllipsizeMode.MIDDLE)
            expander.set_label_widget(expander_label)

            expander_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4, margin_start=14)
            expander.add(expander_box)

            details_grid = Gtk.Grid(row_spacing=4, column_spacing=14)
            expander_box.pack_start(details_grid, False, False, 0)
            row = 0

            details_grid.attach(Gtk.Label(label="Status:", halign=Gtk.Align.START), 0, row, 1, 1)
            details_grid.attach(Gtk.Label(label=f"<span foreground='{PROOF_KIND_FG_COLORS[proof.kind()]}'>{proof.kind().to_str()}</span>", use_markup=True, halign=Gtk.Align.START), 1, row, 1, 1)
            row += 1

            details_grid.attach(Gtk.Label(label="Prover:", halign=Gtk.Align.START), 0, row, 1, 1)
            details_grid.attach(Gtk.Label(label=proof.details().used_prover(), halign=Gtk.Align.START), 1, row, 1, 1)
            row += 1

            details_grid.attach(Gtk.Label(label="Comorphism:", halign=Gtk.Align.START), 0, row, 1, 1)
            details_grid.attach(Gtk.Label(label=comorphism.name(), halign=Gtk.Align.START, ellipsize=Pango.EllipsizeMode.MIDDLE, tooltip_text=comorphism.name()), 1, row, 1, 1)
            row += 1

            used_axioms_box = Gtk.FlowBox(column_spacing=8, row_spacing=4)
            used_axioms = proof.details().used_axioms()
            for axiom in used_axioms:
                sentence = theory.sentence_by_name(axiom)
                axiom_label = Gtk.Label(label=axiom, tooltip_text=str(sentence) if sentence else axiom)
                axiom_label.get_style_context().add_class("axiom")
                used_axioms_box.add(axiom_label)

            details_grid.attach(Gtk.Label(label="Used axioms:", halign=Gtk.Align.START), 0, row, 1, 1)
            details_grid.attach(used_axioms_box, 1, row, 1, 1)
            row += 1

            details_grid.attach(Gtk.Label(label="Time used:", halign=Gtk.Align.START), 0, row, 1, 1)
            # used_time = time.strftime("%H:%M:%S", proof.details().used_time())
            used_time = proof.details().used_time()
            details_grid.attach(Gtk.Label(label=used_time, halign=Gtk.Align.START), 1, row, 1, 1)
            row += 1

            tactic_script = proof.details().tactic_script()
            ts_regex = [
                re.compile(r"^ATPTacticScript \{tsTimeLimit = (\d+), tsExtraOpts = \[(.*)\]\}$"),
                re.compile(r"^TacticScript \{timeLimit = (\d+), extraOptions = \[(.*)\]\}$")
            ]
            ts_time, ts_opts = None, None

            for regex in ts_regex:
                match = regex.match(tactic_script)
                if match:
                    ts_time = match.group(1)
                    ts_opts_list = match.group(2)
                    list_regex = re.compile(r"\"((?:\\\"|[^\"])*)\"")
                    ts_opts = []
                    for match in list_regex.finditer(ts_opts_list):
                        ts_opts.append(match.group(1))

                    break

            if ts_time is not None and ts_opts is not None:
                details_grid.attach(Gtk.Label(label="Time limit:", halign=Gtk.Align.START), 0, row, 1, 1)
                details_grid.attach(Gtk.Label(label=f"{ts_time}s", halign=Gtk.Align.START), 1, row, 1, 1)
                row += 1

                details_grid.attach(Gtk.Label(label="Extra options:", halign=Gtk.Align.START), 0, row, 1, 1)
                details_grid.attach(Gtk.Label(label=" ".join(ts_opts), halign=Gtk.Align.START), 1, row, 1, 1)
                row += 1
            else:
                details_grid.attach(Gtk.Label(label="Tactic script:", halign=Gtk.Align.START), 0, row, 1, 1)
                details_grid.attach(Gtk.Label(label=proof.details().tactic_script(), halign=Gtk.Align.START), 1, row, 1, 1)
                row += 1

            proof_tree_text = proof.details().proof_tree().strip()
            proof_tree_widget = DotWidget()
            proof_tree_widget.get_style_context().add_class("proof-tree")
            if proof_tree_text != "" and proof_tree_widget.set_dotcode(proof_tree_text.encode("utf-8")):
                proof_tree_widget.set_size_request(-1, 800)
            else:
                proof_tree_widget.destroy()
                proof_tree_widget = Gtk.Label(label=proof_tree_text, halign=Gtk.Align.START)

            proof_tree_expander = Gtk.Expander(label="Proof tree:", hexpand=True)
            proof_tree_expander.add(proof_tree_widget)
            expander_box.pack_start(proof_tree_expander, False, False, 0)
            # details_grid.attach(proof_tree_expander, 0, row, 2, 1)
            # row += 1

            proof_lines_expander = Gtk.Expander(label="Proof lines:", hexpand=True)
            proof_lines_widget = Gtk.Label(label="\n".join(proof.details().proof_lines()), halign=Gtk.Align.START, selectable=True, lines=len(proof.details().proof_lines()), wrap=True)
            proof_lines_widget.get_style_context().add_class("proof-lines")
            # proof_lines_widget = Gtk.TextView()
            # proof_lines_widget.set_property('editable', False)
            # proof_lines_widget.set_property('monospace', True)
            # text_buffer = proof_lines_widget.get_buffer()
            # text_buffer.set_text("\n".join(proof.details().proof_lines()))
            proof_lines_expander.add(proof_lines_widget)
            expander_box.pack_start(proof_lines_expander, False, False, 0)
            # details_grid.attach(proof_lines_expander, 0, row, 2, 1)
            # row += 1

            self.box.pack_start(expander, False, True, 4)

        self.show_all()
