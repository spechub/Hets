from OCC.Display.SimpleGui import *
from OCC import BRep
from OCC.BRepTools import *
from OCC import TopoDS
from OCC.Message import Message_PrinterOStream
from OCC.TopoDS import TopoDS_Shape



fileName = input('please insert file path and name:')
brep_instance = BRepTools()
shape = TopoDS.TopoDS_Shape()
builder = BRep.BRep_Builder()
outputString = ""
printrerStream = Message_PrinterOStream()
s = printrerStream.GetStream()
brep_instance.Read(shape, str(fileName), builder)
brep_instance.Dump(shape, s)