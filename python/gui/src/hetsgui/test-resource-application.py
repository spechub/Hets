import logging
import os.path
import sys
from typing import List

import gi

from utils import resource_exist

gi.require_version("Gtk", "3.0")


from gi.repository import Gtk, Gio, GObject, GLib


def get_test_window_for_window_resource(resource_name: str):
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
    

class PreviewWidgetWindow(Gtk.Window):
    def __init__(self, resource: str, **kwargs):
        super().__init__(**kwargs)
        self.set_default_size(400, 400)
        import widgets
        
        widget_name = resource.split("/")[-1]
        widget_class = widgets.__dict__[widget_name]
        widget = widget_class()
        self.add(widget)


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
                # if resource.endswith("Window.ui"):
                if resource.endswith("/"):
                    result += collect_resources(path + resource)
                elif resource.endswith(".ui"):
                    result.append(path + resource[:-3])

            return result

        resources = collect_resources("/eu/hets/")
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

        check_button = Gtk.CheckButton(label="Use stub class", active=True)

        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        box.pack_start(self.combo, False, False, 0)

        button_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL)
        button_box.pack_start(button, True, True, 14)
        button_box.pack_end(check_button, False, False, 0)

        box.pack_start(button_box, False, False, 0)

        self._check_stub = check_button

        self.add(box)

    def on_open_clicked(self, widget):
        resource_model = self.combo.get_model()
        selected = self.combo.get_active()
        resource = resource_model[selected][0]
        self.emit("preview-resource", resource)

    def use_stub(self) -> bool:
        return self._check_stub.get_active()


class PreviewApplication(Gtk.Application):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.window = None

        pgk_dir = os.path.realpath(os.path.join(os.path.dirname(os.path.realpath(__file__)), ""))
        resource_file = os.path.join(pgk_dir, "hetsgui.gresource")
        resource: Gio.Resource = Gio.resource_load(resource_file)
        Gio.resources_register(resource)

        self.add_main_option("log", ord('l'), GLib.OptionFlags.NONE, GLib.OptionArg.STRING, "Log level", "<debug|info|warning|error>")
        self.connect("handle-local-options", self.on_handle_local_options)

        # noinspection PyUnresolvedReferences
        import widgets

    def on_handle_local_options(self, application, options: GLib.VariantDict):
        log_value = options.lookup_value("log")
        if log_value is not None:
            log_level = log_value.get_string().upper()
            log_level_int = getattr(logging, log_level.upper(), None)
            if not isinstance(log_level_int, int):
                print('Invalid log level: %s' % log_level, file=sys.stderr)
                return 1
            logging.basicConfig(level=log_level_int)

        return -1

    def do_activate(self):
        if not self.window:
            resource_selector_window = ResourceSelectorWindow(application=self)
            resource_selector_window.connect("preview-resource", self.preview_resource)

            self.window = resource_selector_window

        self.window.show_all()
        self.window.present()

    def preview_resource(self, widget, resource):
        use_stub = True
        if self.window is not None:
            self.window.close()
            use_stub = self.window.use_stub()

        if resource.endswith("Window"):
            if use_stub:
                template_window = get_test_window_for_window_resource(resource)(application=self)
                self.window = template_window
            else:
                import importlib
                module_name = resource[len("/eu/hets/"):].replace("/", ".")
                window_module = importlib.import_module(module_name)
                window_type = window_module.__dict__[resource.split("/")[-1]]
                window = window_type(application=self)
                self.window = window
        else:
            self.window = PreviewWidgetWindow(resource, application=self)

        self.window.show_all()
        self.window.present()



if __name__ == "__main__":
    app = PreviewApplication()
    exit_status = app.run(sys.argv)
    sys.exit(exit_status)
