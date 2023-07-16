import gi
from gi.repository import Gtk, GObject

from GtkSmartTemplate import GtkSmartTemplate
from hets import Comorphism, Prover, Theory

@GtkSmartTemplate
class ProverComorphismSelector(Gtk.Grid):
    __gtype_name__ = "ProverComorphismSelector"
    
    _prover_model: Gtk.ListStore = Gtk.Template.Child()
    _comorphism_model: Gtk.ListStore = Gtk.Template.Child()
    _comorphism_filtered: Gtk.TreeModelFilter = Gtk.Template.Child()
    
    _combo_comorphism: Gtk.ComboBox = Gtk.Template.Child()
    _combo_prover: Gtk.ComboBox = Gtk.Template.Child()
    
    theory = GObject.Property()

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        
        self.connect('notify::theory', self.on_theory_changed)

    def on_theory_changed(self, *args):
        if self.theory is None:
            return
            
        # Add provers and comorphisms to their respective models for display in combo boxes
        for prover, comorphisms in self.theory.get_usable_provers_with_comorphisms().items():
            shortest_comorphism_path_len = 100
            for comorphism in comorphisms:
                comorphism_path_length = comorphism.path_length()
                if comorphism_path_length < shortest_comorphism_path_len:
                    shortest_comorphism_path_len = comorphism_path_length

                self._comorphism_model.append(
                    [comorphism.name(), comorphism.name(), prover.name(), comorphism_path_length])

            shortest_comorphism_path_len = min(
                c.path_length() for c in comorphisms)
            self._prover_model.append(
                [prover.name(), prover.name(), shortest_comorphism_path_len])

        self._comorphism_filtered.set_visible_func(self._comorphism_filter)
        self._combo_prover.set_active(0)
        
    @GObject.Property()
    def selected_comorphism(self) -> Comorphism:
        comorphism_model = self._combo_comorphism.get_model()
        comorphism_index = self._combo_comorphism.get_active()
        comorphism_name = comorphism_model[comorphism_index][0] if comorphism_index >= 0 else None
        comorphism = None if comorphism_name is None else next(
            c for c in self.theory.get_available_comorphisms() if c.name() == comorphism_name)
        return comorphism

    @GObject.Property()
    def selected_prover(self) -> Prover:
        prover_model = self._combo_prover.get_model()
        prover_index = self._combo_prover.get_active()
        prover_name = prover_model[prover_index][0] if prover_index >= 0 else None
        prover = self.theory.get_prover_by_name(prover_name)
        return prover

    def _comorphism_filter(self, model: Gtk.ListStore, path: str, data):
        prover_model = self._combo_prover.get_model()
        active_prover_iter = self._combo_prover.get_active_iter()

        if active_prover_iter is not None:
            prover_name = prover_model[active_prover_iter][0]
            return model[path][2] == prover_name
        else:
            return False

    @Gtk.Template.Callback()
    def update_comorphisms(self, widget):
        self._comorphism_filtered.refilter()
        if len(self._comorphism_filtered) > 0:
            self._combo_comorphism.set_active(0)