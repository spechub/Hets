import os
import hets

from typing import List

from gi.repository import GLib, Gtk, Gdk, Pango, Gio

from widgets.GraphvizGraphWidget import GraphvizGraphWidget


class defaultview(object):
    w, h = 10, 10
    xy: List[int]

class MainWindow(Gtk.ApplicationWindow):
    def __init__(self, file: str, **kwargs):
        super().__init__(**kwargs)

        self.file = file
        self.library = hets.load_library(file)

        self.set_size_request(1200, 600)

        self.box = Gtk.Box(spacing=6)
        self.add(self.box)

        w = GraphvizGraphWidget(self.library.development_graph())
        self.box.pack_start(w, True, True, 0)


        self.set_title(f"{file} - Hets")

        self.connect("button-press-event", self.on_click)
        # self.add(w)

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

