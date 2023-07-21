# For debugging purposes don't load hyphen. It takes too long for a short test of the UI
try:
    import hyphen

    from .EdgeInfoDialog import EdgeInfoDialog
    from .NodeInfoDialog import NodeInfoDialog
    from .GraphvizGraphWidget import GraphvizGraphWidget
    from .NodeInfoDialog import NodeInfoDialog
    from .ProofDetail import ProofDetail
    from .GridWithToolComorphismSelector import GridWithToolComorphismSelector
except:
    pass

from .CellRendererLink import CellRendererLink
from .SelectableTreeView import SelectableTreeView
from .ExtendedDotWidget import ExtendedDotWidget
from .EditableListView import EditableListView
