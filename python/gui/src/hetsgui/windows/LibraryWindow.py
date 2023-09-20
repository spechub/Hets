import logging

from graphviz import Digraph

import hets

from gi.repository import Gtk

from ..GtkSmartTemplate import GtkSmartTemplate
from ..widgets import ExtendedDotWidget


def library_to_dot_graph(library: hets.Library):
    g = Digraph("G")
    for name, _ in library.environment():
        g.node(str(name), label=str(name))

    return g.source


@GtkSmartTemplate
class LibraryWindow(Gtk.Window):
    __gtype_name__ = "LibraryWindow"

    _logger = logging.getLogger(__name__)
    _ui_graph: ExtendedDotWidget = Gtk.Template.Child()
    _library: hets.Library

    def __init__(self, library: hets.Library, **kwargs):
        super().__init__(**kwargs)
        self._library = library

        self._ui_graph.set_dotcode(library_to_dot_graph(library))



