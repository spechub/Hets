import sys

import gi

gi.require_version("Gtk", "3.0")
from gi.repository import GLib, Gtk, Gio

class MyApplication(Gtk.Application):
    def __init__(self):
        super().__init__(
            application_id="eu.hets.hets",
            flags=Gio.ApplicationFlags.HANDLES_OPEN)
        GLib.set_application_name("Hets")
        self.set_option_context_parameter_string("FILE")

        self.connect("open", self.on_open)

        self.window = None
        self.file = None

    def _set_menu(self):
        file_menu = Gio.Menu()

        menu_entry_open = Gio.MenuItem()
        menu_entry_open.set_label("Open")
        menu_entry_open.set_action_and_target_value("win.open_file", None)
        file_menu.append_item(menu_entry_open)

        view_menu = Gio.Menu()
        menu_entry_show_hide_names = Gio.MenuItem()
        menu_entry_show_hide_names.set_label("Show internal names")
        menu_entry_show_hide_names.set_action_and_target_value("win.toggle_show_names", None)
        view_menu.append_item(menu_entry_show_hide_names)

        menu_entry_show_hide_nodes = Gio.MenuItem()
        menu_entry_show_hide_nodes.set_label("Show unnamed nodes without open proofs")
        menu_entry_show_hide_nodes.set_action_and_target_value("win.toggle_show_nodes", None)
        view_menu.append_item(menu_entry_show_hide_nodes)

        menu_entry_show_hide_edges = Gio.MenuItem()
        menu_entry_show_hide_edges.set_label("Show newly added proven edges")
        menu_entry_show_hide_edges.set_action_and_target_value("win.toggle_show_edges", None)
        view_menu.append_item(menu_entry_show_hide_edges)

        proof_menu = Gio.Menu()
        menu_entry_automatic = Gio.MenuItem()
        menu_entry_automatic.set_label("Apply proof rules automatically")
        menu_entry_automatic.set_action_and_target_value("win.proofs.automatic", None)
        proof_menu.append_item(menu_entry_automatic)

        menu_entry_global_subsume = Gio.MenuItem()
        menu_entry_global_subsume.set_label("Global-Subsumption")
        menu_entry_global_subsume.set_action_and_target_value("win.proofs.global_subsume", None)
        proof_menu.append_item(menu_entry_global_subsume)

        menu_entry_global_decomposition = Gio.MenuItem()
        menu_entry_global_decomposition.set_label("Global-Decomposition")
        menu_entry_global_decomposition.set_action_and_target_value("win.proofs.global_decomposition", None)
        proof_menu.append_item(menu_entry_global_decomposition)

        menu_entry_local_inference = Gio.MenuItem()
        menu_entry_local_inference.set_label("Local-Inference")
        menu_entry_local_inference.set_action_and_target_value("win.proofs.local_inference", None)
        proof_menu.append_item(menu_entry_local_inference)

        menu_entry_local_decomposition = Gio.MenuItem()
        menu_entry_local_decomposition.set_label("Local-Decomposition")
        menu_entry_local_decomposition.set_action_and_target_value("win.proofs.local_decomposition", None)
        proof_menu.append_item(menu_entry_local_decomposition)

        menu_entry_composition_prove_edges = Gio.MenuItem()
        menu_entry_composition_prove_edges.set_label("Prove composed edges")
        menu_entry_composition_prove_edges.set_action_and_target_value("win.proofs.composition_prove_edges", None)
        proof_menu.append_item(menu_entry_composition_prove_edges)

        menu_entry_conservativity = Gio.MenuItem()
        menu_entry_conservativity.set_label("Conservativity")
        menu_entry_conservativity.set_action_and_target_value("win.proofs.conservativity", None)
        proof_menu.append_item(menu_entry_conservativity)

        menu_entry_automatic_hide_theorem_shift = Gio.MenuItem()
        menu_entry_automatic_hide_theorem_shift.set_label("Hide-Theorem-Shift")
        menu_entry_automatic_hide_theorem_shift.set_action_and_target_value("win.proofs.automatic_hide_theorem_shift", None)
        proof_menu.append_item(menu_entry_automatic_hide_theorem_shift)

        menu_entry_theorem_hide_shift = Gio.MenuItem()
        menu_entry_theorem_hide_shift.set_label("Theorem-Hide-Shift")
        menu_entry_theorem_hide_shift.set_action_and_target_value("win.proofs.theorem_hide_shift", None)
        proof_menu.append_item(menu_entry_theorem_hide_shift)

        menu_entry_compute_colimit = Gio.MenuItem()
        menu_entry_compute_colimit.set_label("Compute colimit")
        menu_entry_compute_colimit.set_action_and_target_value("win.proofs.compute_colimit", None)
        proof_menu.append_item(menu_entry_compute_colimit)

        menu_entry_normal_form = Gio.MenuItem()
        menu_entry_normal_form.set_label("Compute normal form")
        menu_entry_normal_form.set_action_and_target_value("win.proofs.normal_form", None)
        proof_menu.append_item(menu_entry_normal_form)

        menu_entry_triangle_cons = Gio.MenuItem()
        menu_entry_triangle_cons.set_label("Triangle-Cons")
        menu_entry_triangle_cons.set_action_and_target_value("win.proofs.triangle_cons", None)
        proof_menu.append_item(menu_entry_triangle_cons)

        menu_entry_freeness = Gio.MenuItem()
        menu_entry_freeness.set_label("Freeness")
        menu_entry_freeness.set_action_and_target_value("win.proofs.freeness", None)
        proof_menu.append_item(menu_entry_freeness)

        menu_entry_lib_flat_imports = Gio.MenuItem()
        menu_entry_lib_flat_imports.set_label("Flatten imports")
        menu_entry_lib_flat_imports.set_action_and_target_value("win.proofs.lib_flat_imports", None)
        proof_menu.append_item(menu_entry_lib_flat_imports)

        menu_entry_lib_flat_d_unions = Gio.MenuItem()
        menu_entry_lib_flat_d_unions.set_label("Flatten D-unions")
        menu_entry_lib_flat_d_unions.set_action_and_target_value("win.proofs.lib_flat_d_unions", None)
        proof_menu.append_item(menu_entry_lib_flat_d_unions)

        menu_entry_lib_flat_renamings = Gio.MenuItem()
        menu_entry_lib_flat_renamings.set_label("Flatten renamings")
        menu_entry_lib_flat_renamings.set_action_and_target_value("win.proofs.lib_flat_renamings", None)
        proof_menu.append_item(menu_entry_lib_flat_renamings)

        menu_entry_lib_flat_hiding = Gio.MenuItem()
        menu_entry_lib_flat_hiding.set_label("Flatten hiding")
        menu_entry_lib_flat_hiding.set_action_and_target_value("win.proofs.lib_flat_hiding", None)
        proof_menu.append_item(menu_entry_lib_flat_hiding)

        menu_entry_lib_flat_heterogen = Gio.MenuItem()
        menu_entry_lib_flat_heterogen.set_label("Flatten heterogen")
        menu_entry_lib_flat_heterogen.set_action_and_target_value("win.proofs.lib_flat_heterogen", None)
        proof_menu.append_item(menu_entry_lib_flat_heterogen)

        menu_entry_qualify_lib_env = Gio.MenuItem()
        menu_entry_qualify_lib_env.set_label("Qualify lib env")
        menu_entry_qualify_lib_env.set_action_and_target_value("win.proofs.qualify_lib_env", None)
        proof_menu.append_item(menu_entry_qualify_lib_env)


        menu = Gio.Menu()
        menu.append_submenu("File", file_menu)
        menu.append_submenu("View", view_menu)
        menu.append_submenu("Proofs", proof_menu)
        self.set_menubar(menu)

    def do_startup(self):
        Gtk.Application.do_startup(self)
        self._set_menu()

    def on_action_open_file(self, action, parameter):
        print("Hello World!")

    def do_command_line(self, command_line):
        options = command_line.get_options_dict()
        # convert GVariantDict -> GVariant -> dict
        options = options.end().unpack()

        self.activate()
        return 0

    def on_open(self, a, files, n_files, hint):
        if n_files != 1:
            print("Expected exactly one file")
            return 1

        self.file = files[0].get_path()
        self.do_activate()

    def do_activate(self):
        if not self.window:
            from windows.MainWindow import MainWindow
            self.window = MainWindow(application=self)

            if self.file:
                self.window.open_file(self.file)

        print(self.get_app_menu())
        self.window.show_all()
        self.window.present()

app = MyApplication()
exit_status = app.run(sys.argv)
sys.exit(exit_status)
