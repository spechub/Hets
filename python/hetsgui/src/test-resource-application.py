import os.path
import sys
from typing import List

import gi

from utils import resource_exist

gi.require_version("Gtk", "3.0")


from gi.repository import Gtk, Gio, GObject


def get_test_window_for_resource(resource_name: str):
    name = resource_name.split("/")[-1]
    style_resource_name = f"{resource_name}.css"

    @Gtk.Template(resource_path=f"{resource_name}.ui")
    class PreviewWindow(Gtk.Window):
        __gtype_name__ = name

        def __init__(self, **kwargs):
            super().__init__(**kwargs)

            if resource_exist(style_resource_name):
                provider = Gtk.CssProvider()
                provider.load_from_resource(style_resource_name)
                self.get_style_context().add_provider(provider, Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)

    return PreviewWindow


class ResourceSelectorWindow(Gtk.Window):
    __gsignals__ = {
        "preview-resource": (GObject.SignalFlags.RUN_FIRST, None, (str,))
    }

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

        def collect_resources(path: str):
            rs: List[str] = Gio.resources_enumerate_children(path, 0)
            result = []
            for resource in rs:
                if resource.endswith("Window.ui"):
                    result.append(path + resource[:-3])
                elif resource.endswith("/"):
                    result += collect_resources(path + resource)

            return result

        resources = collect_resources("/eu/hets/gui/")
        resource_model = Gtk.ListStore(str)

        for r in resources:
            resource_model.append([r])

        self.combo: Gtk.ComboBox = Gtk.ComboBox.new_with_model(resource_model)
        renderer_text = Gtk.CellRendererText()
        self.combo.pack_start(renderer_text, True)
        self.combo.add_attribute(renderer_text, "text", 0)
        self.combo.set_active(0)

        button = Gtk.Button(label="Open")
        button.connect("clicked", self.on_open_clicked)

        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        box.pack_start(self.combo, False, False, 0)
        box.pack_start(button, False, False, 0)

        self.add(box)

    def on_open_clicked(self, widget):
        resource_model = self.combo.get_model()
        selected = self.combo.get_active()
        resource = resource_model[selected][0]
        self.emit("preview-resource", resource)


class PreviewApplication(Gtk.Application):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.window = None

        pgk_dir = os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), ""))
        resource_file = os.path.join(pgk_dir, "hetsgui.gresource")
        resource: Gio.Resource = Gio.resource_load(resource_file)
        Gio.resources_register(resource)

        # noinspection PyUnresolvedReferences
        import widgets

    def do_activate(self):
        if not self.window:
            resource_selector_window = ResourceSelectorWindow(application=self)
            resource_selector_window.connect("preview-resource", self.preview_resource)

            self.window = resource_selector_window

        self.window.show_all()
        self.window.present()

    def preview_resource(self, widget, resource):
        if self.window is not None:
            self.window.close()

        template_window = get_test_window_for_resource(resource)(application=self)
        self.window = template_window

        self.window.show_all()
        self.window.present()



if __name__ == "__main__":
    app = PreviewApplication()
    exit_status = app.run(sys.argv)
    sys.exit(exit_status)
