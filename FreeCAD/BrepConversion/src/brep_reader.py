from OCC.Display.SimpleGui import *
from OCC import BRep
from OCC.BRepTools import *
from OCC import TopoDS
from OCC.Message import Message_PrinterOStream
import sys



fileName = 'input.brp'
if (len(sys.argv) > 1):
    fileName = sys.argv[1]

brep_instance = BRepTools()
shape = TopoDS.TopoDS_Shape()
builder = BRep.BRep_Builder()
printrerStream = Message_PrinterOStream()
s = printrerStream.GetStream()
brep_instance.Read(shape, str(fileName), builder)

