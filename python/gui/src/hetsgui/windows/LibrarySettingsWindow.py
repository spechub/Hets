import logging
import typing
from typing import Dict, Any

from gi.repository import Gtk, GObject

from hets import Options
from ..GtkSmartTemplate import GtkSmartTemplate
from ..widgets import EditableListView


def natural_case(s: str) -> str:
    return s.capitalize().replace("_", " ")


@GtkSmartTemplate
class LibrarySettingsWindow(Gtk.Window):
    """
    A generic window to edit the library settings.
    """
    _widgets: dict[str, Gtk.Widget]
    _next_row: int

    __gtype_name__ = "LibrarySettingsWindow"

    __gsignals__ = {"apply-settings": (GObject.SIGNAL_RUN_FIRST, None, (GObject.TYPE_PYOBJECT,))}
    _logger = logging.getLogger(__name__)

    _grid: Gtk.Grid = Gtk.Template.Child()

    def __init__(self, settings: typing.Optional[Options] = None, **kwargs):
        super().__init__(**kwargs)

        self._next_row = 0
        self._widgets = {}

        if settings is None:
            settings = Options()

        self._settings = settings

        # Add fields for each option dynamically
        for option in sorted(list(settings), key=lambda o: o.name):
            name, typ = option.name, option.typ
            if typ == bool:
                self._add_bool_field(name)
            elif typ == str:
                self.add_string_field(name)
            elif typ == int:
                self.add_int_field(name)
            elif isinstance(typ, list):
                self.add_list_field(name, typ[0])
            else:
                self._logger.warning(f"Field '%s' has unknown type '%s'", name, typ)

    def _add_row(self, field_name: str, widget: Gtk.Widget):
        """
        Helper function to add a row to the grid with a label and a widget.

        :param field_name: The name of the field.
        :param widget: The widget to add.
        :return:
        """
        label = Gtk.Label(label=natural_case(field_name), halign=Gtk.Align.START)
        self._grid.attach(label, 0, self._next_row, 1, 1)
        self._grid.attach(widget, 1, self._next_row, 1, 1)
        self._next_row += 1

        self._widgets[field_name] = widget

    def _add_bool_field(self, name: str):
        """
        Adds a boolean field to the grid.
        :param name: The name of the field.
        :return:
        """

        widget = Gtk.Switch(active=self._settings[name], halign=Gtk.Align.END, valign=Gtk.Align.CENTER)
        self._add_row(name, widget)

    def add_string_field(self, name: str):
        """
        Adds a string field to the grid.

        :param name: The name of the field.
        :return:
        """

        widget = Gtk.Entry(text=self._settings[name], halign=Gtk.Align.FILL, hexpand=True, valign=Gtk.Align.CENTER)
        self._add_row(name, widget)

    def add_int_field(self, name: str):
        """
        Adds an integer field to the grid.
        :param name: The name of the field.
        :return:
        """

        widget = Gtk.SpinButton(value=self._settings[name], halign=Gtk.Align.FILL, hexpand=True,
                                valign=Gtk.Align.CENTER)
        widget.set_range(0, 2 ** 64 - 1)
        self._add_row(name, widget)

    def add_list_field(self, name: str, item_type):
        """
        Adds a list field to the grid.

        :param name: The name of the field
        :param item_type: The type of the items in the list.
        :return:
        """

        widget = EditableListView()
        num_args = len(item_type) if isinstance(item_type, tuple) else 1
        model = Gtk.ListStore(*[str for _ in range(num_args)])
        values = list(self._settings[name])
        for value in values:
            if num_args == 1:
                model.append([value])
            else:
                model.append(list(value))

        widget.model = model
        self._add_row(name, widget)

    @Gtk.Template.Callback()
    def on_apply_clicked(self, *args):
        """
        Updates the settings and emits the apply-settings signal.

        :param args:
        :return:
        """

        for name, widget in self._widgets.items():
            if isinstance(widget, Gtk.Switch):
                self._settings[name] = widget.get_active()
            elif isinstance(widget, Gtk.SpinButton):
                self._settings[name] = widget.get_value_as_int()
            elif isinstance(widget, Gtk.Entry):
                self._settings[name] = widget.get_text()
            elif isinstance(widget, EditableListView):
                entries = [tuple(list(x)) if len(list(x)) > 1 else x[0] for x in widget.model]
                self._settings[name] = entries

        self._logger.debug("Library settings: %s", self._settings.to_dict())

        self.emit('apply-settings', self._settings)

    @Gtk.Template.Callback()
    def on_cancel_clicked(self, *args):
        self.close()
