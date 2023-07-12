import os
import typing

import hets

from typing import List, Callable, Any, Optional

from gi.repository import GLib, Gtk, Gio

from widgets.EdgeInfoDialog import EdgeInfoDialog
from widgets.GraphvizGraphWidget import GraphvizGraphWidget
from widgets.NodeInfoDialog import NodeInfoDialog

from windows.ProveWindow import ProveWindow


T = typing.TypeVar("T")


class defaultview(object):
    w, h = 10, 10
    xy: List[int]


class MainWindow(Gtk.ApplicationWindow):
    ui_box: Gtk.Box
    ui_graph: GraphvizGraphWidget
    file: Optional[str]
    library: Optional[hets.Library]

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.file = None
        self.library = None

        self.set_auto_startup_notification(True)
        self.set_size_request(1200, 600)
        self.set_title("Heterogeneous Toolset")
        icon = os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../resources/icon.png"))
        self.set_default_icon_from_file(icon)
        self.set_icon_from_file(icon)

        self.ui_box = Gtk.Box(spacing=6)
        self.add(self.ui_box)

        self.ui_graph = GraphvizGraphWidget()
        self.ui_box.pack_start(self.ui_graph, True, True, 0)

        self._action("open_file", self.on_menu_open_file)
        self._action("node.prove", self.on_prove_node, "s")
        self._action("node.show_info", self.on_show_node_info, "s")
        self._action("edge.show_info", self.on_show_edge_info, "av")
        self._action_toggle("toggle_show_names", self.on_toggle_show_names)
        self._action_toggle("toggle_show_nodes", self.on_toggle_show_nodes)
        self._action_toggle("toggle_show_edges", self.on_toggle_show_edges)

        self._action("proofs.automatic", self.on_automatic)
        self._action("proofs.global_subsume", self.on_global_subsume)
        self._action("proofs.global_decomposition", self.on_global_decomposition)
        self._action("proofs.local_inference", self.on_local_inference)
        self._action("proofs.local_decomposition", self.on_local_decomposition)
        self._action("proofs.composition_prove_edges", self.on_composition_prove_edges)
        self._action("proofs.conservativity", self.on_conservativity)
        self._action("proofs.automatic_hide_theorem_shift", self.on_automatic_hide_theorem_shift)
        self._action("proofs.theorem_hide_shift", self.on_theorem_hide_shift)
        self._action("proofs.compute_colimit", self.on_compute_colimit)
        self._action("proofs.normal_form", self.on_normal_form)
        self._action("proofs.triangle_cons", self.on_triangle_cons)
        self._action("proofs.freeness", self.on_freeness)
        self._action("proofs.lib_flat_imports", self.on_lib_flat_imports)
        self._action("proofs.lib_flat_d_unions", self.on_lib_flat_d_unions)
        self._action("proofs.lib_flat_renamings", self.on_lib_flat_renamings)
        self._action("proofs.lib_flat_hiding", self.on_lib_flat_hiding)
        self._action("proofs.lib_flat_heterogen", self.on_lib_flat_heterogen)
        self._action("proofs.qualify_lib_env", self.on_qualify_lib_env)

    def _action(self, name: str, cb: Callable[[Gio.SimpleAction, T], Any], param_type_str: Optional[str] = None) -> Gio.SimpleAction:
        action = Gio.SimpleAction.new(name, GLib.VariantType(param_type_str) if param_type_str else None)
        action.connect("activate", cb)
        self.add_action(action)
        return action

    def _action_toggle(self, name: str, cb: Callable[[Gio.SimpleAction, bool], Any], default: bool = False) -> Gio.SimpleAction:
        action = Gio.SimpleAction.new_stateful(name, None,  GLib.Variant.new_boolean(default))
        action.connect("change-state", cb)
        self.add_action(action)
        return action

    def open_file(self, file: str):
        self.file = file
        self.library = hets.load_library(file)

        if self.ui_graph:
            self.ui_graph.load_graph(self.library.development_graph())

        self.set_title(f"{file} - Heterogeneous Toolset")

    def on_menu_open_file(self, action: Gio.SimpleAction, parameter: str):
        dialog = Gtk.FileChooserDialog(
            title="Please choose a file", parent=self, action=Gtk.FileChooserAction.OPEN
        )
        dialog.add_buttons(
            Gtk.STOCK_CANCEL,
            Gtk.ResponseType.CANCEL,
            Gtk.STOCK_OPEN,
            Gtk.ResponseType.OK,
        )

        filter_text = Gtk.FileFilter()
        filter_text.set_name("Text files")
        filter_text.add_mime_type("text/plain")
        dialog.add_filter(filter_text)

        filter_any = Gtk.FileFilter()
        filter_any.set_name("Any files")
        filter_any.add_pattern("*")
        dialog.add_filter(filter_any)

        response = dialog.run()
        file = None
        if response == Gtk.ResponseType.OK:
            file = dialog.get_filename()

        dialog.destroy()

        if file:
            self.open_file(file)

    def on_prove_node(self, action, parameter: GLib.Variant):
        node_id = parameter.get_string()
        if self.library:
            node = [n for n in self.library.development_graph().nodes() if str(n.id()) == node_id][0]

            prove_window = ProveWindow(node, transient_for=self)
            prove_window.show_all()
            prove_window.present()

            prove_window.connect("destroy", lambda _: self.ui_graph.render())

            # node.prove(node.theory().get_prover_by_name("Pellet"))

            # self.ui_graph.render()
        else:
            print(f'Action: prove node {node_id}. But no library is loaded!')

    def on_show_node_info(self, action, parameter: GLib.Variant):
        node_id = parameter.get_string()
        if self.library:
            node = [n for n in self.library.development_graph().nodes() if str(n.id()) == node_id][0]

            info_dialog = NodeInfoDialog(self, node)
            info_dialog.run()
        else:
            print(f'Action: Show info for node {node_id}. But no library is loaded!')

    def on_show_edge_info(self, action, parameter: GLib.Variant):
        origin_id = parameter.get_child_value(0).get_child_value(0).get_string()
        target_id = parameter.get_child_value(1).get_child_value(0).get_string()
        if self.library:
            edge = [e for e in self.library.development_graph().edges() if str(e.origin()) == origin_id and str(e.target()) == target_id][0]

            info_dialog = EdgeInfoDialog(self, edge)
            info_dialog.run()
        else:
            print(f'Action: Show info for edge {origin_id}->{target_id}. But no library is loaded!')

    def on_toggle_show_names(self, action: Gio.SimpleAction, target: GLib.Variant):
        action.set_state(target)
        state = target.get_boolean()

        if state:
            self.ui_graph.show_internal_node_names()
        else:
            self.ui_graph.hide_internal_node_names()

    def on_toggle_show_nodes(self, action: Gio.SimpleAction, target: GLib.Variant):
        action.set_state(target)
        state = target.get_boolean()

        if state:
            self.ui_graph.show_unnamed_nodes_without_open_proofs()
        else:
            self.ui_graph.hide_unnamed_nodes_without_open_proofs()

    def on_toggle_show_edges(self, action: Gio.SimpleAction, target: GLib.Variant):
        action.set_state(target)
        state = target.get_boolean()

        if state:
            self.ui_graph.show_newly_added_proven_edges()
        else:
            self.ui_graph.hide_newly_added_proven_edges()

    def on_automatic(self, action: Gio.SimpleAction, target):
        self.library.automatic()
        self.ui_graph.render()

    def on_global_subsume(self, action: Gio.SimpleAction, target):
        self.library.global_subsume()
        self.ui_graph.render()

    def on_global_decomposition(self, action: Gio.SimpleAction, target):
        self.library.global_decomposition()
        self.ui_graph.render()

    def on_local_inference(self, action: Gio.SimpleAction, target):
        self.library.local_inference()
        self.ui_graph.render()

    def on_local_decomposition(self, action: Gio.SimpleAction, target):
        self.library.local_decomposition()
        self.ui_graph.render()

    def on_composition_prove_edges(self, action: Gio.SimpleAction, target):
        self.library.composition_prove_edges()
        self.ui_graph.render()

    def on_conservativity(self, action: Gio.SimpleAction, target):
        self.library.conservativity()
        self.ui_graph.render()

    def on_automatic_hide_theorem_shift(self, action: Gio.SimpleAction, target):
        self.library.automatic_hide_theorem_shift()
        self.ui_graph.render()

    def on_theorem_hide_shift(self, action: Gio.SimpleAction, target):
        self.library.theorem_hide_shift()
        self.ui_graph.render()

    def on_compute_colimit(self, action: Gio.SimpleAction, target):
        self.library.compute_colimit()
        self.ui_graph.render()

    def on_normal_form(self, action: Gio.SimpleAction, target):
        self.library.normal_form()
        self.ui_graph.render()

    def on_triangle_cons(self, action: Gio.SimpleAction, target):
        self.library.triangle_cons()
        self.ui_graph.render()

    def on_freeness(self, action: Gio.SimpleAction, target):
        self.library.freeness()
        self.ui_graph.render()

    def on_lib_flat_imports(self, action: Gio.SimpleAction, target):
        self.library.lib_flat_imports()
        self.ui_graph.render()

    def on_lib_flat_d_unions(self, action: Gio.SimpleAction, target):
        self.library.lib_flat_d_unions()
        self.ui_graph.render()

    def on_lib_flat_renamings(self, action: Gio.SimpleAction, target):
        self.library.lib_flat_renamings()
        self.ui_graph.render()

    def on_lib_flat_hiding(self, action: Gio.SimpleAction, target):
        self.library.lib_flat_hiding()
        self.ui_graph.render()

    def on_lib_flat_heterogen(self, action: Gio.SimpleAction, target):
        self.library.lib_flat_heterogen()
        self.ui_graph.render()

    def on_qualify_lib_env(self, action: Gio.SimpleAction, target):
        self.library.qualify_lib_env()
        self.ui_graph.render()
