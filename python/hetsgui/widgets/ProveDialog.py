from gi.repository import Gtk

from hets import DevGraphNode

ui = """

"""

class ProveDialog(Gtk.Window):
    def __init__(self, node: DevGraphNode):
        super().__init__(title=f"Prove {node.name()}")
