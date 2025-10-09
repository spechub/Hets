import logging

from gi.repository import Gtk

from .utils import resource_exist


def GtkSmartTemplate(original_class):
    """
    An extension to the Gtk.Template decorator that also loads a css file from the resources.

    Uses the name of the module of the class to determine the path to the resources.

    :param original_class: The class to decorate.
    :return: The decorated class.
    """

    _logger = logging.getLogger(__name__)

    # The module name follows the format `hetsgui.path.to.file`.
    # The resources are organized under `/eu/hets/gui/path/to/file`.
    resource_name = "/".join(original_class.__module__.split(".")[1:])
    style_resource_name = f"/eu/hets/gui/{resource_name}.css"

    original_init = original_class.__init__

    def new_init(self, *args, **kwargs):
        original_init(self, *args, **kwargs)

        if resource_exist(style_resource_name):
            _logger.debug("Loading css resource %s", style_resource_name)
            self._provider = Gtk.CssProvider()
            self._provider.load_from_resource(style_resource_name)
            self.get_style_context().add_provider_for_screen(self.get_screen(), self._provider, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)

            self.connect("destroy", lambda w: self.get_style_context().remove_provider_for_screen(self.get_screen(), self._provider))

    original_class.__init__ = new_init

    return Gtk.Template(resource_path=f"/eu/hets/gui/{resource_name}.ui")(original_class)
