import logging
import os
import typing

import hets

from typing import List, Callable, Any, Optional

from gi.repository import GLib, Gtk, Gio, GObject

from hets import Library, ReferenceDevGraphNode, LibName, Options
from ..GtkSmartTemplate import GtkSmartTemplate
from ..utils import get_variant
from ..widgets.EdgeInfoDialog import EdgeInfoDialog
from ..widgets.GraphvizGraphWidget import GraphvizGraphWidget
from ..widgets.NodeInfoDialog import NodeInfoDialog
from ..widgets.TheoryInfoDialog import TheoryInfoDialog
from ..windows.LibrarySettingsWindow import LibrarySettingsWindow

from ..windows.ProveWindow import ProveWindow
from ..windows.ConsistencyCheckWindow import ConsistencyCheckWindow
from ..windows.ConservativityCheckWindow import ConservativityCheckWindow
from ..windows.LibraryWindow import LibraryWindow

T = typing.TypeVar("T")


class defaultview(object):
    w, h = 10, 10
    xy: List[int]


@GtkSmartTemplate
class MainWindow(Gtk.ApplicationWindow):
    __gtype_name__ = "MainWindow"
    __gsignals__ = {
        "load-file": (GObject.SIGNAL_RUN_FIRST, None, (str, object)),
        "show-library": (GObject.SIGNAL_RUN_FIRST, None, (str,)),
        "show-library-graph": (GObject.SIGNAL_RUN_FIRST, None, (str,)),
    }

    _logger = logging.getLogger(__name__)

    _library_settings_window: Optional[LibrarySettingsWindow]
    _settings: hets.Options
    _ui_graph: GraphvizGraphWidget = Gtk.Template.Child()
    _status_bar: Gtk.Statusbar = Gtk.Template.Child()
    _loaded_library: Optional[hets.Library]

    def __init__(self, settings: Optional[Options] = None, **kwargs):
        super().__init__(**kwargs)
        self._library_settings_window = None
        self._settings = hets.Options(
            libdirs=[os.environ["HETS_LIB"]] if "HETS_LIB" in os.environ else []) if settings is None else settings
        self._loaded_library = None

        self._ui_graph.connect("render-start",
                               lambda _: self._status_bar.push(self._status_bar.get_context_id("render"),
                                                               "Rendering graph ..."))
        self._ui_graph.connect("render-end", lambda _: self._status_bar.push(self._status_bar.get_context_id("render"),
                                                                             "Graph rendered!"))

        self.set_auto_startup_notification(True)
        icon = os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), "../resources/icon.png"))
        self.set_default_icon_from_file(icon)
        self.set_icon_from_file(icon)

        self._library_actions: typing.List[Gio.SimpleAction] = []

        self._action("open_file", self._on_menu_open_file)

        self._library_actions.append(self._action("open_library_window", self._on_open_library_window))

        self._action_state("change_graph_layout", self._on_change_graph_layout, "vertical")

        self._library_actions.append(self._action("node.prove", self._on_prove_node, "s"))
        self._library_actions.append(self._action("node.check_consistency", self._on_check_consistency_node, "s"))
        self._library_actions.append(self._action("node.show_info", self._on_show_node_info, "s"))
        self._library_actions.append(self._action("node.show_theory", self._on_show_theory, "s"))
        self._library_actions.append(self._action("node.translate", self._on_translate_node, "av"))
        self._library_actions.append(
            self._action("edge.check_conservativity", self._on_check_conservativity_edge, "av"))
        self._library_actions.append(self._action("edge.show_info", self._on_show_edge_info, "av"))

        self._library_actions.append(self._action_toggle("toggle_show_names", self._on_toggle_show_names))
        self._library_actions.append(self._action_toggle("toggle_show_edges", self._on_toggle_show_edges))

        self._library_actions.append(self._action("proofs.automatic", self.on_automatic))
        self._library_actions.append(self._action("proofs.global_subsume", self.on_global_subsume))
        self._library_actions.append(self._action("proofs.global_decomposition", self.on_global_decomposition))
        self._library_actions.append(self._action("proofs.local_inference", self.on_local_inference))
        self._library_actions.append(self._action("proofs.local_decomposition", self.on_local_decomposition))
        self._library_actions.append(self._action("proofs.composition_prove_edges", self.on_composition_prove_edges))
        self._library_actions.append(self._action("proofs.conservativity", self.on_conservativity))
        self._library_actions.append(
            self._action("proofs.automatic_hide_theorem_shift", self.on_automatic_hide_theorem_shift))
        self._library_actions.append(self._action("proofs.theorem_hide_shift", self.on_theorem_hide_shift))
        self._library_actions.append(self._action("proofs.compute_colimit", self.on_compute_colimit))
        self._library_actions.append(self._action("proofs.normal_form", self.on_normal_form))
        self._library_actions.append(self._action("proofs.triangle_cons", self.on_triangle_cons))
        self._library_actions.append(self._action("proofs.freeness", self.on_freeness))
        self._library_actions.append(self._action("proofs.lib_flat_imports", self.on_lib_flat_imports))
        self._library_actions.append(self._action("proofs.lib_flat_d_unions", self.on_lib_flat_d_unions))
        self._library_actions.append(self._action("proofs.lib_flat_renamings", self.on_lib_flat_renamings))
        self._library_actions.append(self._action("proofs.lib_flat_hiding", self.on_lib_flat_hiding))
        self._library_actions.append(self._action("proofs.lib_flat_heterogen", self.on_lib_flat_heterogen))
        self._library_actions.append(self._action("proofs.qualify_lib_env", self.on_qualify_lib_env))

        self._library_actions.append(self._action("open_win_for_lib_by_node", self._on_open_win_for_lib_by_node, "i"))

        self._action("open_library_settings", self.on_open_library_settings)

        self._set_library_actions_enabled(False)

    def _set_library_actions_enabled(self, enabled: bool):
        for action in self._library_actions:
            action.set_enabled(enabled)

    def _action(self, name: str, cb: Callable[[Gio.SimpleAction, T], Any],
                param_type_str: Optional[str] = None, target: Optional[Gio.ActionMap] = None) -> Gio.SimpleAction:
        action = Gio.SimpleAction.new(name, GLib.VariantType(param_type_str) if param_type_str else None)
        action.connect("activate", cb)

        if target is None:
            self.add_action(action)
        else:
            target.add_action(action)
        return action

    def _action_toggle(self, name: str, cb: Callable[[Gio.SimpleAction, GLib.Variant], Any],
                       default: bool = False) -> Gio.SimpleAction:
        return self._action_state(name, cb, default, None)

    def _action_state(self, name: str, cb: Callable[[Gio.SimpleAction, GLib.Variant], Any], default: Optional[T] = None,
                      param_type_str: Optional[str | typing.Literal["infer"]] = "infer") -> Gio.SimpleAction:

        default_variant = get_variant(default)
        if param_type_str == "infer":
            param_type = default_variant.get_type()
        elif param_type_str is not None:
            param_type = GLib.VariantType(param_type_str)
        else:
            param_type = None

        action = Gio.SimpleAction.new_stateful(name, param_type, default_variant)
        action.connect("change-state", cb)
        self.add_action(action)
        return action

    def use_library(self, library: Library):
        self._loaded_library = library

        if self._ui_graph:
            self._ui_graph.load_graph(self._loaded_library.development_graph())

        self.set_title(f"{library.name().id()} - Heterogeneous Toolset")

        self._set_library_actions_enabled(True)

    def _on_change_graph_layout(self, action: Gio.SimpleAction, parameter: GLib.Variant):
        action.set_state(parameter)

        direction = parameter.get_string()

        self._logger.debug(f"Changing graph layout to {direction}")

        self._ui_graph.graph_direction = direction

    def _on_open_library_window(self, action: Gio.SimpleAction, parameter: str):
        self.emit("show-library-graph", self._loaded_library.name().id())

    def _on_menu_open_file(self, action: Gio.SimpleAction, parameter: str):
        dialog = Gtk.FileChooserDialog(
            title="Please choose a file", parent=self, action=Gtk.FileChooserAction.OPEN
        )

        for libdir in self._settings["libdirs"]:
            dialog.add_shortcut_folder(libdir)

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
            self.emit("load-file", file, self._settings)

    def _on_prove_node(self, action, parameter: GLib.Variant):
        node_id = parameter.get_string()
        if self._loaded_library:
            node = [n for n in self._loaded_library.development_graph().nodes() if str(n.id()) == node_id][0]

            prove_window = ProveWindow(node, transient_for=self)
            prove_window.show_all()
            prove_window.present()

            prove_window.connect("destroy", lambda _: self._ui_graph.render())
        else:
            self._logger.warning(f'Action: prove node {node_id}. But no library is loaded!')

    def _on_check_consistency_node(self, action, parameter: GLib.Variant):
        node_id = parameter.get_string()
        if self._loaded_library:
            node = [n for n in self._loaded_library.development_graph().nodes() if str(n.id()) == node_id][0]

            check_consistency_window = ConsistencyCheckWindow(node, transient_for=self)
            check_consistency_window.show_all()
            check_consistency_window.present()

            check_consistency_window.connect("destroy", lambda _: self._ui_graph.render())
        else:
            self._logger.warning(f'Action: check consistency node {node_id}. But no library is loaded!')

    def _on_show_node_info(self, action, parameter: GLib.Variant):
        node_id = parameter.get_string()
        if self._loaded_library:
            node = [n for n in self._loaded_library.development_graph().nodes() if str(n.id()) == node_id][0]

            info_dialog = NodeInfoDialog(node)
            info_dialog.run()
            info_dialog.destroy()
        else:
            self._logger.warning(f'Action: Show info for node {node_id}. But no library is loaded!')

    def _on_translate_node(self, action, parameter: GLib.Variant):
        node_id = parameter.get_child_value(0).get_child_value(0).get_string()
        comorphism_name = parameter.get_child_value(1).get_child_value(0).get_string()
        if self._loaded_library:
            node = [n for n in self._loaded_library.development_graph().nodes() if str(n.id()) == node_id][0]
            comorphism = next((c for c in node.global_theory().get_available_comorphisms() if c.name() == comorphism_name), None)

            if comorphism is None:
                self._logger.error("Could not find comorphism")
            else:
                translated = node.global_theory().translate(comorphism)
                info_dialog = TheoryInfoDialog(translated, node.name())
                info_dialog.run()
                info_dialog.destroy()
        else:
            self._logger.warning(f'Action: Show info for node {node_id}. But no library is loaded!')

    def _on_show_theory(self, action, parameter: GLib.Variant):
        node_id = parameter.get_string()
        if self._loaded_library:
            node = [n for n in self._loaded_library.development_graph().nodes() if str(n.id()) == node_id][0]

            info_dialog = TheoryInfoDialog(node.global_theory(), node.name())
            info_dialog.run()
            info_dialog.destroy()
        else:
            self._logger.warning(f'Action: Show info for node {node_id}. But no library is loaded!')

    def _on_show_edge_info(self, action, parameter: GLib.Variant):
        origin_id = parameter.get_child_value(0).get_child_value(0).get_string()
        target_id = parameter.get_child_value(1).get_child_value(0).get_string()
        if self._loaded_library:
            edge = [e for e in self._loaded_library.development_graph().edges() if
                    str(e.origin()) == origin_id and str(e.target()) == target_id][0]

            info_dialog = EdgeInfoDialog(edge)
            info_dialog.run()
        else:
            self._logger.warning(f'Action: Show info for edge {origin_id}->{target_id}. But no library is loaded!')

    def _on_check_conservativity_edge(self, action, parameter: GLib.Variant):
        origin_id = parameter.get_child_value(0).get_child_value(0).get_string()
        target_id = parameter.get_child_value(1).get_child_value(0).get_string()
        if self._loaded_library:
            edge = [e for e in self._loaded_library.development_graph().edges() if
                    str(e.origin()) == origin_id and str(e.target()) == target_id][0]

            check_conservativity_window = ConservativityCheckWindow(edge, transient_for=self)
            check_conservativity_window.show_all()
            check_conservativity_window.present()

            check_conservativity_window.connect("destroy", lambda _: self._ui_graph.render())
        else:
            self._logger.warning(f'Action: Show info for edge {origin_id}->{target_id}. But no library is loaded!')

    def _on_toggle_show_names(self, action: Gio.SimpleAction, target: GLib.Variant):
        action.set_state(target)
        state = target.get_boolean()

        if state:
            self._ui_graph.show_internal_node_names()
        else:
            self._ui_graph.hide_internal_node_names()

    def _on_toggle_show_edges(self, action: Gio.SimpleAction, target: GLib.Variant):
        action.set_state(target)
        state = target.get_boolean()

        if state:
            self._ui_graph.show_newly_added_proven_edges()
        else:
            self._ui_graph.hide_newly_added_proven_edges()

    def on_automatic(self, action: Gio.SimpleAction, target):
        self._loaded_library.automatic()
        self._ui_graph.render()

    def on_global_subsume(self, action: Gio.SimpleAction, target):
        self._loaded_library.global_subsume()
        self._ui_graph.render()

    def on_global_decomposition(self, action: Gio.SimpleAction, target):
        self._loaded_library.global_decomposition()
        self._ui_graph.render()

    def on_local_inference(self, action: Gio.SimpleAction, target):
        self._loaded_library.local_inference()
        self._ui_graph.render()

    def on_local_decomposition(self, action: Gio.SimpleAction, target):
        self._loaded_library.local_decomposition()
        self._ui_graph.render()

    def on_composition_prove_edges(self, action: Gio.SimpleAction, target):
        self._loaded_library.composition_prove_edges()
        self._ui_graph.render()

    def on_conservativity(self, action: Gio.SimpleAction, target):
        self._loaded_library.conservativity()
        self._ui_graph.render()

    def on_automatic_hide_theorem_shift(self, action: Gio.SimpleAction, target):
        self._loaded_library.automatic_hide_theorem_shift()
        self._ui_graph.render()

    def on_theorem_hide_shift(self, action: Gio.SimpleAction, target):
        self._loaded_library.theorem_hide_shift()
        self._ui_graph.render()

    def on_compute_colimit(self, action: Gio.SimpleAction, target):
        self._loaded_library.compute_colimit()
        self._ui_graph.render()

    def on_normal_form(self, action: Gio.SimpleAction, target):
        self._loaded_library.normal_form()
        self._ui_graph.render()

    def on_triangle_cons(self, action: Gio.SimpleAction, target):
        self._loaded_library.triangle_cons()
        self._ui_graph.render()

    def on_freeness(self, action: Gio.SimpleAction, target):
        self._loaded_library.freeness()
        self._ui_graph.render()

    def on_lib_flat_imports(self, action: Gio.SimpleAction, target):
        self._loaded_library.lib_flat_imports()
        self._ui_graph.render()

    def on_lib_flat_d_unions(self, action: Gio.SimpleAction, target):
        self._loaded_library.lib_flat_d_unions()
        self._ui_graph.render()

    def on_lib_flat_renamings(self, action: Gio.SimpleAction, target):
        self._loaded_library.lib_flat_renamings()
        self._ui_graph.render()

    def on_lib_flat_hiding(self, action: Gio.SimpleAction, target):
        self._loaded_library.lib_flat_hiding()
        self._ui_graph.render()

    def on_lib_flat_heterogen(self, action: Gio.SimpleAction, target):
        self._loaded_library.lib_flat_heterogen()
        self._ui_graph.render()

    def on_qualify_lib_env(self, action: Gio.SimpleAction, target):
        self._loaded_library.qualify_lib_env()
        self._ui_graph.render()

    def on_open_library_settings(self, action: Gio.SimpleAction, target):
        if self._library_settings_window is None:
            self._library_settings_window = LibrarySettingsWindow(settings=self._settings)
            self._library_settings_window.connect('apply-settings', self._on_settings_changed)

        self._library_settings_window.show_all()
        self._library_settings_window.present()

    def _on_settings_changed(self, widget, settings: hets.Options):
        self._settings = settings

        self._library_settings_window.close()
        self._library_settings_window = None

        if self._loaded_library is not None:
            self.emit("load-file", self._loaded_library.name().location(), self._settings)

    def _on_open_win_for_lib_by_node(self, action: Gio.SimpleAction, parameter: GLib.Variant):
        if self._loaded_library is None:
            return

        node_id = parameter.get_int32()
        node = self._loaded_library.development_graph().node_by_id(node_id)
        if node is None:
            self._logger.error(
                f"Attempted to load referenced library for node {node_id} but the node could not be found in the development graph.")

            dialog = Gtk.MessageDialog(transient_for=self, flags=0, message_type=Gtk.MessageType.ERROR,
                                       buttons=Gtk.ButtonsType.CLOSE, text=f"Failed to referenced library!")
            dialog.format_secondary_text(
                f"The node of the referenced library was not found in the development graph. Please contact the developers.")
            dialog.run()
            dialog.destroy()

        if isinstance(node, ReferenceDevGraphNode):
            lib_name = node.referenced_libname()
            self.emit("show-library", lib_name.id())

        else:
            self._logger.error(
                f"Attempted to load referenced library for node {node_id} but the node is not a reference node!")

            dialog = Gtk.MessageDialog(transient_for=self, flags=0, message_type=Gtk.MessageType.ERROR,
                                       buttons=Gtk.ButtonsType.CLOSE, text=f"Failed to referenced library!")
            dialog.format_secondary_text(
                f"The node of the referenced library is not a reference node. Please contact the developers.")
            dialog.run()
            dialog.destroy()
