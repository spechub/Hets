import re
import typing
from typing import Any

from gi.repository import GLib, Gio


def get_variant_type(t: type):
    if t == str:
        return GLib.VariantType.new("s")
    if t == int:
        return GLib.VariantType("i")
    if t == dict:
        return GLib.VariantType("a{sv}")
    if t in [list, tuple, set]:
        return GLib.VariantType("av")

    raise Exception(f"Unknown data type: {t}")


def get_variant(data: Any) -> GLib.Variant:
    # Source: https://gitlab.gnome.org/GNOME/gnome-browser-connector/-/blob/master/gnome_browser_connector/helpers.py
    # Licenced under GPL-3.0-or-later

    if isinstance(data, str):
        return GLib.Variant.new_string(data)
    elif isinstance(data, bool):
        return GLib.Variant.new_boolean(data)
    elif isinstance(data, int):
        return GLib.Variant.new_int32(data)
    elif isinstance(data, (list, tuple, set)):
        variant_builder: GLib.VariantBuilder = GLib.VariantBuilder.new(GLib.VariantType.new('av'))

        for value in data:
            variant_builder.add_value(GLib.Variant.new_variant(get_variant(value)))

        return variant_builder.end()
    elif isinstance(data, dict):
        variant_builder = GLib.VariantBuilder.new(GLib.VariantType.new('a{sv}'))

        for key in data:
            if data[key] is None:
                continue

            key_string = str(key)

            variant_builder.add_value(
                GLib.Variant.new_dict_entry(
                    get_variant(key_string), GLib.Variant.new_variant(get_variant(data[key]))
                )
            )

        return variant_builder.end()
    else:
        raise Exception(f"Unknown data type: {type(data)}")


def resource_exist(resource_path: str) -> bool:
    segments = [s for s in re.split(r"([^/]+/)", resource_path) if s]
    segments.reverse()
    path = segments.pop()
    while segments:
        segment = segments.pop()
        children = Gio.resources_enumerate_children(path, 0)
        if segment not in children:
            return False
        path += segment
    return True
