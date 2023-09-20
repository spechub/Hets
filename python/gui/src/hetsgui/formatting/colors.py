from gi.repository import Gdk

from hets import ProofKind, ConsistencyKind

PROOF_KIND_BG_COLORS = {
    ProofKind.UNKNOWN: "fuchsia",
    ProofKind.OPEN: "white",
    ProofKind.PROVEN: "limegreen",
    ProofKind.PROVEN_BY_INCONSISTENCY: "orange",
    ProofKind.DISPROVEN: "coral",
    ProofKind.TIMED_OUT: "royalblue",
    ProofKind.GUESSED: "darkseagreen",
    ProofKind.CONJECTURED: "darkseagreen",
    ProofKind.HANDWRITTEN: "darkseagreen"
}

PROOF_KIND_FG_COLORS = {
    ProofKind.UNKNOWN: "fuchsia",
    ProofKind.OPEN: "black",
    ProofKind.PROVEN: "limegreen",
    ProofKind.PROVEN_BY_INCONSISTENCY: "orange",
    ProofKind.DISPROVEN: "coral",
    ProofKind.TIMED_OUT: "royalblue",
    ProofKind.GUESSED: "darkseagreen",
    ProofKind.CONJECTURED: "darkseagreen",
    ProofKind.HANDWRITTEN: "darkseagreen"
}

CONSISTENCY_KIND_BG_COLORS = {
    ConsistencyKind.INCONSISTENT: "red",
    ConsistencyKind.UNKNOWN: "black",
    ConsistencyKind.PROOF_THEORETICALLY_CONSERVATIVE: "darkgreen",
    ConsistencyKind.CONSERVATIVE: "green",
    ConsistencyKind.MONOMORPHIC: "violet",
    ConsistencyKind.DEFINITIONAL: "darkseagreen",
    ConsistencyKind.TIMED_OUT: "blue",
    ConsistencyKind.ERROR: "darkred",
}


def color_name_to_rgba(color_name: str) -> Gdk.RGBA:
    color = Gdk.RGBA()
    color.parse(color_name)
    return color


def color_to_hex(color: Gdk.RGBA) -> str:
    red = int(color.red * 255)
    green = int(color.green * 255)
    blue = int(color.blue * 255)
    return f"#{red:02x}{green:02x}{blue:02x}"


# KEY: (colorname, variant, light)
COLOR_MAP = {
    ("black", False, False): "gray0"
    , ("black", False, True): "gray30"
    , ("blue", False, False): "RoyalBlue3"
    , ("blue", False, True): "RoyalBlue1"
    , ("blue", True, False): "SteelBlue3"
    , ("blue", True, True): "SteelBlue1"
    , ("coral", False, False): "coral3"
    , ("coral", False, True): "coral1"
    , ("coral", True, False): "LightSalmon2"
    , ("coral", True, True): "LightSalmon"
    , ("green", False, False): "MediumSeaGreen"
    , ("green", False, True): "PaleGreen3"
    , ("green", True, False): "limegreen"
    , ("green", True, True): "LightGreen"
    , ("purple", False, False): "purple2"
    , ("yellow", False, False): "gold"
    , ("yellow", False, True): "yellow"
    , ("yellow", True, False): "LightGoldenrod3"
    , ("yellow", True, True): "LightGoldenrod"
    , ("fuchsia", False, False): "fuchsia"
    , ("fuchsia", False, True): "fuchsia"
    , ("fuchsia", True, False): "fuchsia"
    , ("fuchsia", True, True): "fuchsia"
}
