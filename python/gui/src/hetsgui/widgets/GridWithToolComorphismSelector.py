import typing

from gi.repository import Gtk, GObject

from ..GtkSmartTemplate import GtkSmartTemplate
from hets import Comorphism, ConsistencyChecker, Prover, Theory


@GtkSmartTemplate
class GridWithToolComorphismSelector(Gtk.Grid):
    __gtype_name__ = "GridWithToolComorphismSelector"

    _tool_model: Gtk.ListStore = Gtk.Template.Child()
    _comorphism_model: Gtk.ListStore = Gtk.Template.Child()
    _comorphism_filtered: Gtk.TreeModelFilter = Gtk.Template.Child()

    _combo_comorphism: Gtk.ComboBox = Gtk.Template.Child()
    _combo_tool: Gtk.ComboBox = Gtk.Template.Child()
    _lbl_tool: Gtk.Label = Gtk.Template.Child()
    _lbl_comorphism: Gtk.Label = Gtk.Template.Child()

    theory: Theory = GObject.Property()
    use_consistency_checkers: bool = GObject.Property(type=bool, default=False)
    start_top: int = GObject.Property(type=int, default=0)
    start_left: int = GObject.Property(type=int, default=0)

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        self.connect('notify::theory', self._update)
        self.connect('notify::use-consistency-checkers', self._update)
        self.connect('notify::start-top', self._reorganize_widgets)
        self.connect('notify::start-left', self._reorganize_widgets)

    def _reorganize_widgets(self, *args):
        self.child_set_property(self._lbl_tool, "top-attach", self.start_top)
        self.child_set_property(self._combo_tool, "top-attach", self.start_top)
        self.child_set_property(self._lbl_comorphism, "top-attach", self.start_top + 1)
        self.child_set_property(self._combo_comorphism, "top-attach", self.start_top + 1)

        self.child_set_property(self._lbl_tool, "left-attach", self.start_left)
        self.child_set_property(self._combo_tool, "left-attach", self.start_left + 1)
        self.child_set_property(self._lbl_comorphism, "left-attach", self.start_left)
        self.child_set_property(self._combo_comorphism, "left-attach", self.start_left + 1)

    def _update(self, *args):
        if self.theory is None:
            return

        self._lbl_tool.set_label("Consistency checker:" if self.use_consistency_checkers else "Prover:")

        self._tool_model.clear()
        self._comorphism_model.clear()

        # Add provers and comorphisms to their respective models for display in combo boxes
        tool_with_comorphism = self.theory.get_usable_consistency_checkers_with_comorphisms() if self.use_consistency_checkers else self.theory.get_usable_provers_with_comorphisms()
        for tool, comorphisms in tool_with_comorphism.items():
            shortest_comorphism_path_len = 100
            for comorphism in comorphisms:
                comorphism_path_length = comorphism.path_length()
                if comorphism_path_length < shortest_comorphism_path_len:
                    shortest_comorphism_path_len = comorphism_path_length

                self._comorphism_model.append(
                    [comorphism.name(), comorphism.name(), tool.name(), comorphism_path_length])

            shortest_comorphism_path_len = min(
                c.path_length() for c in comorphisms)
            self._tool_model.append(
                [tool.name(), tool.name(), shortest_comorphism_path_len])

        self._comorphism_filtered.set_visible_func(self._comorphism_filter)
        self._combo_tool.set_active(0)

    @GObject.Property()
    def selected_comorphism(self) -> typing.Optional[Comorphism]:
        comorphism_model = self._combo_comorphism.get_model()
        comorphism_index = self._combo_comorphism.get_active()
        comorphism_name = comorphism_model[comorphism_index][0] if comorphism_index >= 0 else None
        comorphism = None if comorphism_name is None else next(
            c for c in self.theory.get_available_comorphisms() if c.name() == comorphism_name)
        return comorphism

    @GObject.Property()
    def selected_prover(self) -> Prover:
        prover_model = self._combo_tool.get_model()
        prover_index = self._combo_tool.get_active()
        prover_name = prover_model[prover_index][0] if prover_index >= 0 else None
        prover = self.theory.get_prover_by_name(prover_name)
        return prover

    @GObject.Property()
    def selected_consistency_checker(self) -> ConsistencyChecker:
        prover_model = self._combo_tool.get_model()
        prover_index = self._combo_tool.get_active()
        cc_name = prover_model[prover_index][0] if prover_index >= 0 else None
        cc = self.theory.get_consistency_checker_by_name(cc_name)
        return cc

    def _comorphism_filter(self, model: Gtk.TreeModelFilter, path: Gtk.TreeIter, data):
        prover_model = self._combo_tool.get_model()
        active_prover_iter = self._combo_tool.get_active_iter()

        if active_prover_iter is not None:
            prover_name = prover_model[active_prover_iter][0]
            return model[path][2] == prover_name
        else:
            return False

    @Gtk.Template.Callback()
    def update_comorphisms(self, *args):
        self._comorphism_filtered.refilter()
        if len(self._comorphism_filtered) > 0:
            self._combo_comorphism.set_active(0)
