import typing

import hets

from typing import List, Callable, Any, Optional

from gi.repository import GLib, Gtk, Gdk, Pango, Gio

from widgets.GraphvizGraphWidget import GraphvizGraphWidget


T = typing.TypeVar("T")


class defaultview(object):
    w, h = 10, 10
    xy: List[int]


class MainWindow(Gtk.ApplicationWindow):
    ui_box: Gtk.Box
    ui_graph: GraphvizGraphWidget
    file: Optional[str]

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.file = None
        self.library = None

        self.ui_box = Gtk.Box(spacing=6)
        self.add(self.ui_box)

        self.ui_graph = GraphvizGraphWidget()
        self.ui_box.pack_start(self.ui_graph, True, True, 0)


        self.set_size_request(1200, 600)
        self.set_title("Heterogeneous Toolset")

        self.connect("button-press-event", self.on_click)

        self._action("open_file", self.on_menu_open_file)

    def _action(self, name: str, cb) -> Gio.SimpleAction:
        action = Gio.SimpleAction.new(name)
        action.connect("activate", cb)
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

        filter_py = Gtk.FileFilter()
        filter_py.set_name("Python files")
        filter_py.add_mime_type("text/x-python")
        dialog.add_filter(filter_py)

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

    def on_click(self, element, event):

        if event.button == 3:  # on right click
            a1 = Gio.SimpleAction.new("action", int)
            a1.set_enabled(True)
            a1.connect("activate", lambda action, value: print(f"Activate1: {action}, {value}"))

            self.add_action(a1)

            menu = Gtk.Menu()
            m1 = Gtk.MenuItem(label="Action 1", action_name="win.action", action_target=1)
            menu.add(m1)
            m2 = Gtk.MenuItem(label="Action 2", action_name="win.action", action_target=2)
            menu.add(m2)

            menu.attach_to_widget(self)
            menu.show_all()
            menu.popup_at_pointer(event)

