import logging

import gi
import xdot
from gi.repository import Gtk, GObject, Gdk
from graphviz import Digraph

from xdot.ui import DotWidget

from hetsgui.formatting import color_to_hex


class ExtendedDotWidget(DotWidget):
    """
    Extended version of the xdot.DotWidget.

    Added functionalities:
    - emits signals when a node or edge is right-clicked
    - uses the theme's background color as the graph's background color
    - disables some key bindings (like quitting on 'q')

    """

    __gtype_name__ = "ExtendedDotWidget"

    __gsignals__ = {
        # Emitted when a node is right-clicked.
        "node-right-click": (GObject.SIGNAL_RUN_FIRST, None, (str, object)),

        # Emitted when an edge is right-clicked.
        "edge-right-click": (GObject.SIGNAL_RUN_FIRST, None, (str, str, object))
    }

    _logger = logging.getLogger(__name__)

    dotcode = GObject.Property(type=str)
    """ The dot code to be rendered. """

    def __init__(self):
        super().__init__()

        # Update visualisation when dotcode changes
        self.connect("notify::dotcode", self.on_dotcode_changed)

        # Listen for theme changes
        settings: Gtk.Settings = Gtk.Settings.get_for_screen(self.get_screen())
        settings.connect("notify::gtk-theme-name", lambda w, p: self.render())
        settings.connect("notify::gtk-application-prefer-dark-theme", lambda w, p: self.render())

    def render(self):
        pass

    def get_themed_graph(self):
        """
        Create an empty graph with the theme's background color.

        :return:
        """
        g = Digraph("G")

        success, color = self.get_style_context().lookup_color("theme_bg_color")
        color = color_to_hex(color)

        if color:
            g.graph_attr["bgcolor"] = color

        return g

    def on_dotcode_changed(self, widget, param):
        """
        Propagate the dotcode change to the xdot widget.

        :param widget: ignored
        :param param: ignored
        :return:
        """
        dotcode = self.dotcode.encode("utf8")

        self.set_dotcode(dotcode)

    def on_key_press_event(self, widget, event):
        """
        Supress some key press events to disable functionality like quitting on q, focusing search widget with f etc.

        :param widget: self
        :param event: event
        :return:
        """

        if event.keyval < Gdk.KEY_a or event.keyval > Gdk.KEY_z:
            super().on_key_press_event(widget, event)

    def on_click(self, element, event):
        """
        Handle and propagates right-click events on nodes and edges.

        :param element: the clicked element or None
        :param event: the event
        :return:
        """

        # If element is None, try to get the element at the click position
        if element is None:
            jump = self.get_jump(event.x, event.y)
            element = jump.item if jump is not None else None

        # If element is still None, the click was not on a node or edge
        if element is None:
            return True

        if event.button == 3:  # on right click
            self._logger.debug("Right click on %s", element)
            if isinstance(element, xdot.ui.elements.Node):
                node_id = element.id.decode("utf-8")

                self.emit("node-right-click", node_id, event)
            elif isinstance(element, xdot.ui.elements.Edge):
                src_id, dst_id = element.src.id.decode("utf-8"), element.dst.id.decode("utf-8")

                self.emit("edge-right-click", src_id, dst_id, event)

        return True
