


from typing import Any

from gi.repository import GLib

def get_variant(data: Any) -> GLib.Variant:
    # Source: https://gitlab.gnome.org/GNOME/gnome-browser-connector/-/blob/master/gnome_browser_connector/helpers.py
    # Licenced under GPL-3.0-or-later

    if isinstance(data, str):
        return GLib.Variant.new_string(data)
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

