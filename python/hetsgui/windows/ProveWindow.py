import threading
from typing import Optional

from gi.repository import Gtk, Pango, GLib, Gdk

from hets import DevGraphNode, ProofKind
from formatting.Colors import PROOF_KIND_BG_COLORS, color_name_to_rgba
from widgets.CellRendererLink import CellRendererLink
from windows.ProofDetailsWindow import ProofDetailsWindow


def model_toggle_handle(model, index=1, header: Optional[Gtk.CheckButton] = None):
    def cb(widget, path):
        next_state = not model[path][index]

        model[path][index] = next_state

        if header is not None:
            consistent = all(row[index] == next_state for row in model)
            header.set_inconsistent(not consistent)
            header.set_active(next_state)

    return cb


def model_toggle_column_handle(model, index=1):
    def cb(column: Gtk.TreeViewColumn):
        widget = column.get_widget()
        if not isinstance(widget, Gtk.CheckButton):
            return

        new_state = not (widget.get_inconsistent() or widget.get_active())

        for row in model:
            row[index] = new_state

        widget.set_inconsistent(False)
        widget.set_active(new_state)

    return cb


@Gtk.Template()
class ProveWindow(Gtk.Window):
    def __init__(self, node: DevGraphNode, **kwargs):
        super().__init__(title=f"Prove {node.name()}", **kwargs)
        # def __init__(self, **kwargs):
        #     super().__init__(title=f"Prove {{node.name()}}", **kwargs)
        self.set_default_size(800, -1)
        self.set_position(Gtk.WindowPosition.CENTER_ON_PARENT)
        self.set_destroy_with_parent(True)

        self.proving_thread: Optional[threading.Thread] = None
        self.node = node

        goals = self.goal_widget()
        axioms = self.axioms_widget()
        provers = self.prover_widget()
        prover_settings = self.prover_settings_widget()

        self.header = Gtk.HeaderBar(title=self.get_title())
        self.header.set_show_close_button(True)
        self.btn_prove = Gtk.Button(label="Prove")
        self.header.pack_start(self.btn_prove)
        self.set_titlebar(self.header)

        self.notebook = Gtk.Notebook(tab_pos=Gtk.PositionType.LEFT)
        self.add(self.notebook)

        self.page_prove = provers
        self.page_prove.set_border_width(10)
        self.notebook.append_page(self.page_prove, Gtk.Label(label="Prove"))

        self.page_goals = goals
        self.page_goals.set_border_width(10)
        self.notebook.append_page(self.page_goals, Gtk.Label(label="Goals"))

        self.page_axioms = axioms
        self.page_axioms.set_border_width(10)
        self.notebook.append_page(self.page_axioms, Gtk.Label(label="Axioms"))

        self.page_prover_settings = prover_settings
        self.page_prover_settings.set_border_width(10)
        self.notebook.append_page(self.page_prover_settings, Gtk.Label(label="Prover Settings"))

        self.connect("delete_event", self.on_close)

        self.btn_prove.connect("clicked", self.on_prove_clicked)

    def _goal_style(self, goal):
        proof = goal.best_proof()
        kind = proof.kind() if proof is not None else ProofKind.OPEN
        text = f'<span foreground="black" underline="single">{kind.to_str()}</span>'
        color_name = PROOF_KIND_BG_COLORS[kind]
        color = color_name_to_rgba(color_name)
        return color, text

    def on_close(self, widget, event):
        if self.proving_thread is not None and self.proving_thread.is_alive():
            return True  # Stop the window from being closed if a proving process is currently running

        return False

    def goal_widget(self) -> Gtk.Widget:
        self.goals_model = Gtk.ListStore(str, bool, str, str, str, Gdk.RGBA)

        for goal in self.node.global_theory().goals():
            color, text = self._goal_style(goal)

            self.goals_model.append([goal.name(), True, text, goal.name(), str(goal), color])

        # self.goals_model.append(["Ax5", True, "", 'ClassAssertion( Annotation( :Implied "true"^^:string ) Annotation( :Implied "true"^^xsd:boolean ) :Mother :mary )'])
        # self.goals_model.append(["Ax7", True, "P", 'ClassAssertion( Annotation( :Implied "true"^^:string ) Annotation( :Implied "true"^^xsd:boolean ) :Mother :mary )'])
        # self.goals_model.append(["Ax8", False, "P", 'ClassAssertion( Annotation( :Implied "true"^^:string ) Annotation( :Implied "true"^^xsd:boolean ) :Mother :mary )'])
        # self.goals_model.append(["Ax9", False, "D", 'ClassAssertion( Annotation( :Implied "true"^^:string ) Annotation( :Implied "true"^^xsd:boolean ) :Mother :mary )'])
        # self.goals_model.append(["Ax10", True, "D", 'ClassAssertion( Annotation( :Implied "true"^^:string ) Annotation( :Implied "true"^^xsd:boolean ) :Mother :mary )'])

        treeview = Gtk.TreeView(model=self.goals_model, hexpand=True, hover_expand=True, headers_clickable=True,
                                tooltip_column=4)

        prove_renderer = Gtk.CellRendererToggle()
        prove_all_check: Gtk.CheckButton = Gtk.CheckButton.new()
        prove_all_check.set_active(1)  # By default all goals are selected for proving
        prove_renderer.connect("toggled", model_toggle_handle(self.goals_model, header=prove_all_check))
        prove_column = Gtk.TreeViewColumn("Prove", prove_renderer, active=1)
        prove_column.set_widget(prove_all_check)
        prove_column.set_clickable(True)
        prove_all_check.show_all()
        prove_column.connect("clicked", model_toggle_column_handle(self.goals_model))
        treeview.append_column(prove_column)

        state_renderer = CellRendererLink()
        state_renderer.connect("clicked", self.on_proof_details_clicked)
        state_column = Gtk.TreeViewColumn("State", state_renderer, markup=2, background_rgba=5)
        state_column.set_sort_column_id(2)
        treeview.append_column(state_column)

        name_column = Gtk.TreeViewColumn("Name",
                                         Gtk.CellRendererText(width_chars=20, ellipsize=Pango.EllipsizeMode.END),
                                         text=3)
        name_column.set_sort_column_id(3)
        name_column.set_resizable(True)
        treeview.append_column(name_column)
        goal_column = Gtk.TreeViewColumn("Goal",
                                         Gtk.CellRendererText(width_chars=100, ellipsize=Pango.EllipsizeMode.END),
                                         text=4)
        goal_column.set_sort_column_id(4)
        goal_column.set_resizable(True)
        treeview.append_column(goal_column)

        scrollable_treeview = Gtk.ScrolledWindow(vexpand=True, min_content_height=100)
        scrollable_treeview.add(treeview)

        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)

        box.pack_start(scrollable_treeview, True, True, 0)

        return box

    def axioms_widget(self) -> Gtk.Widget:
        self.axioms_model = Gtk.ListStore(str, bool, str, str)

        for axiom in self.node.global_theory().axioms():
            self.axioms_model.append([axiom.name(), True, axiom.name(), str(axiom)])

        # self.axioms_model.append(["Ax1", True, 'Class: Mother EquivalentTo: Woman and (hasChild some Person)'])
        # self.axioms_model.append(["Ax2", True, 'Class: Woman SubClassOf: Person'])
        # self.axioms_model.append(["Ax3", False, 'Individual: björn Types: Person'])
        # self.axioms_model.append(["Ax4", True, 'Individual: mary Types: Woman '])
        # self.axioms_model.append(["Ax6", False, 'Individual: mary Facts: hasChild john'])

        treeview = Gtk.TreeView(model=self.axioms_model, hexpand=True, headers_clickable=True, tooltip_column=3)

        include_renderer = Gtk.CellRendererToggle()
        include_all_check: Gtk.CheckButton = Gtk.CheckButton.new()
        include_all_check.set_active(1)  # By default all axioms are selected
        include_renderer.connect("toggled", model_toggle_handle(self.axioms_model, header=include_all_check))
        include_column = Gtk.TreeViewColumn("Include", include_renderer, active=1)
        include_column.set_widget(include_all_check)
        include_column.set_clickable(True)
        include_all_check.show_all()
        include_column.connect("clicked", model_toggle_column_handle(self.axioms_model))

        treeview.append_column(include_column)
        name_column = Gtk.TreeViewColumn("Name",
                                         Gtk.CellRendererText(width_chars=20, ellipsize=Pango.EllipsizeMode.END),
                                         text=2)
        name_column.set_sort_column_id(2)
        name_column.set_resizable(True)
        treeview.append_column(name_column)
        axiom_column = Gtk.TreeViewColumn("Axiom",
                                          Gtk.CellRendererText(width_chars=100, ellipsize=Pango.EllipsizeMode.END),
                                          text=3)
        axiom_column.set_sort_column_id(3)
        axiom_column.set_resizable(True)
        treeview.append_column(axiom_column)

        scrollable_treeview = Gtk.ScrolledWindow(vexpand=True, min_content_height=200)
        scrollable_treeview.add(treeview)

        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)

        box.pack_start(scrollable_treeview, True, True, 0)

        return box

    def prover_widget(self) -> Gtk.Widget:
        prover_model = Gtk.ListStore(str, str, int)

        for prover, comorphisms in self.node.global_theory().get_usable_provers_with_comorphisms().items():
            shortest_comorphism_path_len = min(c.path_length() for c in comorphisms)
            prover_model.append([prover.name(), prover.name(), shortest_comorphism_path_len])

        prover_model.set_sort_column_id(2, Gtk.SortType.ASCENDING)

        # prover_model.append(["P_Darwin", "Darwin"])
        # prover_model.append(["P_EProver", "EProver"])
        # prover_model.append(["P_Pellet", "Pellet"])
        # prover_model.append(["P_QuickCheck", "QuickCheck"])

        prover_name_renderer = Gtk.CellRendererText(width_chars=-1, ellipsize=Pango.EllipsizeMode.END)
        self.combo_prover: Gtk.ComboBox = Gtk.ComboBox.new_with_model(prover_model)
        self.combo_prover.pack_start(prover_name_renderer, True)
        self.combo_prover.add_attribute(prover_name_renderer, "text", 1)
        if len(prover_model) > 0:
            self.combo_prover.set_active(0)

        comorphism_model = Gtk.ListStore(str, str, str, int)

        for prover, comorphism in self.node.global_theory().get_usable_provers_and_comorphisms():
            comorphism_model.append([comorphism.name(), prover.name(), comorphism.name(), comorphism.path_length()])
        comorphism_model.set_sort_column_id(3, Gtk.SortType.ASCENDING)

        # comorphism_model.append(["C0", "id_OWL.EL-ALC-D|boolean| : OWL -> OWL"])
        # comorphism_model.append(["C1", "id_OWL.EL-ALC-D|boolean|;OWL2CASL;OWL2TPTP : OWL -> TPTP"])

        comorphism_filtered: Gtk.TreeModelFilter = comorphism_model.filter_new()
        comorphism_filtered.set_visible_func(self._comorphism_filter)

        comorphism_name_renderer = Gtk.CellRendererText(width_chars=-1, ellipsize=Pango.EllipsizeMode.END)
        self.combo_comorphism: Gtk.ComboBox = Gtk.ComboBox.new_with_model(comorphism_filtered)
        self.combo_comorphism.pack_start(comorphism_name_renderer, True)
        self.combo_comorphism.add_attribute(comorphism_name_renderer, "text", 2)

        self._update_comorphisms(self.combo_comorphism)
        self.combo_prover.connect("changed", self._update_comorphisms)

        grid = Gtk.Grid(
            row_homogeneous=False,
            column_spacing=14,
            row_spacing=4
        )

        grid.attach(Gtk.Label(label="Prover:", halign=Gtk.Align.START), 0, 1, 1, 1)
        grid.attach(self.combo_prover, 1, 1, 1, 1)
        grid.attach(Gtk.Label(label="Comorphism:", halign=Gtk.Align.START), 0, 2, 1, 1)
        grid.attach(self.combo_comorphism, 1, 2, 1, 1)

        grid.attach(Gtk.Label(label="Sublogic of theory:", halign=Gtk.Align.START), 0, 3, 1, 1)
        grid.attach(Gtk.Label(label="OWL.EL-ALC-D|boolean|", halign=Gtk.Align.START), 1, 3, 1, 1)

        return grid

    def prover_settings_widget(self) -> Gtk.Widget:
        grid = Gtk.Grid(
            row_homogeneous=False,
            column_spacing=14,
            row_spacing=4
        )

        self.btn_timeout: Gtk.SpinButton = Gtk.SpinButton.new_with_range(0, 2 ** 32 - 1, 1)
        self.btn_timeout.set_value(10)

        self.txt_extra_options = Gtk.Entry()

        self.switch_include_proven_theorems = Gtk.Switch(halign=Gtk.Align.END)

        grid.attach(Gtk.Label(label="Timeout in s:", halign=Gtk.Align.START, hexpand=True), 0, 1, 1, 1)
        grid.attach(self.btn_timeout, 1, 1, 1, 1)
        grid.attach(Gtk.Label(label="Extra options:", halign=Gtk.Align.START), 0, 2, 1, 1)
        grid.attach(self.txt_extra_options, 1, 2, 1, 1)
        grid.attach(Gtk.Label(label="Include proven theorems:", halign=Gtk.Align.START,
                              tooltip_text="Include preceding proven theorems in next proof attempt"), 0, 3, 1, 1)
        grid.attach(self.switch_include_proven_theorems, 1, 3, 1, 1)

        return grid

    def on_prove_clicked(self, _):
        self.proving_thread = threading.Thread(target=self._prove)
        # self.proving_thread.daemon = True
        self.proving_thread.start()

    def _comorphism_filter(self, model, iter, data):
        prover_model = self.combo_prover.get_model()
        active_prover_iter = self.combo_prover.get_active_iter()

        if active_prover_iter is not None:
            prover_name = prover_model[active_prover_iter][0]
            return model[iter][1] == prover_name
        else:
            return False

    def _update_comorphisms(self, _):
        model = self.combo_comorphism.get_model()
        model.refilter()
        if len(model) > 0:
            self.combo_comorphism.set_active(0)

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
            goal_row = next(iter(g for g in self.goals_model if g[0] == prev_goal_name), None)
            goal = next(iter(g for g in self.node.global_theory().goals() if g.name() == prev_goal_name), None)

            if goal_row is not None:
                color, text = self._goal_style(goal)
                goal_row[2] = text
                goal_row[5] = color

        if next_goal_name is not None:
            goal_row = next(iter(g for g in self.goals_model if g[0] == next_goal_name), None)
            if goal_row is not None:
                goal_row[2] = '<span foreground="black" style="italic">Proving...</span>'

    def _finish_prove_progress(self):
        self.btn_prove.set_sensitive(True)
        self.notebook.set_current_page(1)

    @property
    def selected_comorphism(self) -> Optional[str]:
        comorphism_model = self.combo_comorphism.get_model()
        comorphism_index = self.combo_comorphism.get_active()
        return comorphism_model[comorphism_index][0] if comorphism_index >= 0 else None

    def _prove(self):
        GLib.idle_add(self._init_prove_progress)

        goals = [row[0] for row in self.goals_model if row[1]]
        axioms = [row[0] for row in self.axioms_model if row[1]]

        prover_model = self.combo_prover.get_model()
        prover_index = self.combo_prover.get_active()
        prover = prover_model[prover_index][0] if prover_index >= 0 else None

        comorphism_name = self.selected_comorphism
        comorphism = None if comorphism_name is None else next(
            c for c in self.node.global_theory().get_available_comorphisms() if c.name() == comorphism_name)

        timeout = self.btn_timeout.get_value_as_int()

        include_theorems = self.switch_include_proven_theorems.get_active()

        prev_goal = None
        for i, goal in enumerate(goals):
            GLib.idle_add(self._update_prove_progress, goal, prev_goal)

            self.node.prove(self.node.global_theory().get_prover_by_name(prover), comorphism, include_theorems, [goal],
                            axioms,
                            timeout)
            prev_goal = goal

        GLib.idle_add(self._update_prove_progress, None, prev_goal)

        GLib.idle_add(self._finish_prove_progress)

    def on_proof_details_clicked(self, widget, path):
        goal_name = self.goals_model[path][0]
        goal = next(iter(g for g in self.node.global_theory().goals() if g.name() == goal_name), None)

        if goal is not None:
            details_window = ProofDetailsWindow(goal, self.node.global_theory())
            details_window.show_all()
            details_window.present()
