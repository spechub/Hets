# PYTHONPATH=$(realpath ..) python3 main.py

import gi
gi.require_version("Gtk", "4.0")
from gi.repository import Gtk

import hets

def on_activate(app):
    win = Gtk.ApplicationWindow(application=app)
    btn = Gtk.Button(label="Hello, World!")
    btn.connect('clicked', lambda x: win.close())
    win.set_child(btn)
    win.present()

app = Gtk.Application(application_id='org.gtk.Example')
app.connect('activate', on_activate)
app.run(None)
