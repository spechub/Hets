import logging

from gi.repository import Gtk

from hets import DevGraphNode, Theory

INFO_DIALOG_SAVE_RESPONSE = 0x0001_0001


class TheoryInfoDialog(Gtk.Dialog):
    _logger = logging.getLogger(__name__)
    _node: DevGraphNode

    def __init__(self, theory: Theory, name: str):
        super().__init__()

        self.set_default_size(800, 600)

        self.set_title(f"Theory {name}")

        self._theory = theory
        self._name = name

        box = self.get_content_area()
        scrolled_window = Gtk.ScrolledWindow(expand=True)

        text_view = Gtk.TextView()
        text_view.set_property('editable', False)
        text_view.set_property('monospace', True)
        text_buffer = text_view.get_buffer()
        text_buffer.set_text(str(self._theory))

        button_box = self.get_action_area()
        button_box.set_property("margin", 10)
        self.add_button("Save", INFO_DIALOG_SAVE_RESPONSE)

        scrolled_window.add(text_view)
        box.add(scrolled_window)
        # box.add(button)
        self.show_all()

        self.connect("response", self._on_response)

    def _on_response(self, widget: Gtk.Widget, response: int):
        if response == INFO_DIALOG_SAVE_RESPONSE:
            self.stop_emission("response")

            dialog = Gtk.FileChooserDialog(title="Please choose a file", action=Gtk.FileChooserAction.SAVE)
            dialog.add_buttons("Cancel", Gtk.ResponseType.CANCEL,
                               "Save", Gtk.ResponseType.OK)

            dialog.set_current_name(self._name + ".dol")

            filter_dol = Gtk.FileFilter()
            filter_dol.set_name("DOL files")
            filter_dol.add_pattern("*.dol")
            dialog.add_filter(filter_dol)

            filter_any = Gtk.FileFilter()
            filter_any.set_name("Any files")
            filter_any.add_pattern("*")
            dialog.add_filter(filter_any)

            response = dialog.run()

            if response == Gtk.ResponseType.OK:
                filename = dialog.get_filename()
                self._logger.debug("File selected: " + filename)

                with open(filename, "w") as f:
                    f.write(str(self._theory))

            dialog.destroy()

        else:
            self._logger.debug(f"Got unknown response: {response}")
