################################################################################
#
#
#
#
#
#
#
#
#
#
#
#
#
################################################################################

__all__ = [
    "newdoc",
    "fromHets",
]

import sys
sys.path.append('/usr/lib/freecad/lib')
import FreeCAD
import math
import Draft
import Part
from xml.etree import ElementTree as ET

def newdoc(app):
    app.newDocument('fromHets')

def fromHets(filePath, app, gui):
    try:
        f = open (filePath, 'r')
    except IOError as (errno, strerror):
        print "I/O error({0}): {1}".format(errno, strerror)
        return 2
    else:
        s = f.read()
        f.close()
    newdoc(app)
    buildque = []
    objDict = {}
    fcdoc = ET.XML(s)
    for fcobj in fcdoc:
        print fcobj.tag
        name = fcobj.attrib['name']
        print fcobj.attrib
        for props in fcobj:
            if props.tag == 'placement':
                placexml = props.attrib
            else:
                objtype = props.tag
                attribsxml = props.attrib
        print objtype
        entity = name, placexml, attribsxml, objtype, 0
        buildque.append(entity)
        print entity
    while len(buildque) > 0 :
        for elsrc in buildque:
            if isBuildable(elsrc, buildque, app):
                buildObject(elsrc, buildque, objDict, app)
    gui.SendMsgToActiveView('ViewFit')
    gui.activeDocument().activeView().viewAxometric()


#checks whether the object is buildable in the current state of the program
def isBuildable(el, queue, app):
    name, pos, att, ot, tr = el
    hasDependency = False
    composed = ['cut','common','extrude']
    if (ot in composed):
        hasDependency = True
    if hasDependency:
        for it in queue:
            n2, p2, a2, t2 = it
            if att['tool'] == n2:
                return False
            if att['base'] == n2:
                return False
    return True



#calls constructor in the freecad document and updates queue and refList
#arguments: element from buildque, object type, buildque, reference->object dict
def buildObject(el, queue, refList, app): 
    #expand and extract elements needed for object construction
    name, pos, b, objtype, tr = el
    queue.remove(el)
    
    #build the placement from the vector and quaternion stored in the xml file
    base = FreeCAD.Vector(float(pos['x']), float(pos['y']), float(pos['z']))
    quat = [float(pos['q0']), float(pos['q1']), float(pos['q2']), float(pos['q3'])]
    q0, q1, q2, q3 = quat
    angle = 2*math.acos(q3)
    axis = FreeCAD.Vector(q0, q1, q2)
    place = FreeCAD.Placement(base, axis, angle)

    isCreated = False
    defpnt = FreeCAD.Vector()
    defdir = FreeCAD.Vector(0,0,1)
    defplace = FreeCAD.Placement()
    #handler to determine which object constructor to call
    if objtype == 'box':
        isCreated = True
        part = Part.makeBox(float(b['length']), float(b['width']), float(b['height']))
        obj = app.ActiveDocument.addObject('Part::Box',name)
        obj.Shape = part
    elif objtype == 'cylinder':
        isCreated = True
        part = Part.makeCylinder(float(b['radius']), float(b['height']))
        obj = app.ActiveDocument.addObject('Part::Cylinder',name)
        obj.Shape = part
    elif objtype == 'cone':
        isCreated = True
        part = Part.makeCone(float(b['radius1']), float(b['radius2']), float(b['height']))
        obj = app.ActiveDocument.addObject('Part::Cone',name)
        obj.Shape = part
    elif objtype == 'sphere':
        isCreated = True
        part = Part.makeSphere(float(b['radius']), defpnt, defdir, float(b['angle1']),
                               float(b['angle2']),float(b['angle3']))
        obj = app.ActiveDocument.addObject('Part::Sphere',name)
        obj.Shape = part
    elif objtype == 'torus':
        isCreated = True
        print el
        part = Part.makeTorus(float(b['radius1']), float(b['radius2']), defpnt, defdir, 
                              float(b['angle1']),float(b['angle2']),float(b['angle3']))
        obj = app.ActiveDocument.addObject('Part::Torus',name)
        obj.Shape = part
    elif objtype == 'line':
        isCreated = False
        obj = app.ActiveDocument.addObject('Part::Part2DObjectPython', name)
        secpnt = FreeCAD.Vector(float(b['length']),0,0)
        Draft.Wire(obj)
        obj.Points = [defpnt, secpnt]
        obj.Closed = False
        obj.Support = None
    elif objtype == 'circle':
        isCreated = True
        obj = app.ActiveDocument.addObject('Part::Part2DObjectPython', name)
        Circle(obj)
        obj.Radius = float(b['radius'])
        startangle = float(b['angle1'])
        endangle = float(b['angle2'])
        if (startangle != None) and (endangle != None):
            obj.FirstAngle = startangle
            obj.LastAngle = endangle
    elif objtype == 'cut':
        isCreated = True
        obj = addObject('Part::MultiCut',name)
        obj.Shapes = [refList[b['base']],refList[b['tool']]]
    elif objtype == 'fusion':
        isCreated = True
        obj = addObject('Part::MultiFuse',name)
        obj.Shapes = [refList[b['base']],refList[b['tool']]]
        #refList[att['base']].Visibility = False
        #refList[att['tool']].Visibility = False
    elif objtype == 'common':
        isCreated = True
        obj = addObject('Part::MultiCommon',name)
        obj.Shapes = [refList[b['base']],refList[b['tool']]]
    elif objtype == 'extrude':
        isCreated = True
        obj = app.ActiveDocument.addObject('Part::Extrusion', name)
        obj.Base =refList[b['base']]
        obj.Dir = float(FreeCAD.Vector(float(b['valueX']),
                                       float(b['valueY']),
                                       float(b['valueZ'])))
    elif objtype == 'rectangle':
        isCreated = True
        obj = app.ActiveDocument.addObject("Part::Part2DObjectPython",name)
        Draft.Rectangle(obj)
        Draft.ViewProviderRectangle(obj.ViewObject)
        obj.Length = float(b['length'])
        obj.Height = float(b['height'])
        obj.Support =None
        obj.ViewObject.DisplayMode = "Wireframe"
        #Draft.formatObject(obj)
        app.ActiveDocument.recompute()
    
    #all objects are created with the default placement
    #now the actual placement is added to the FreeCAD object
    if isCreated:
        obj.Placement = place
        #add the mapping from the reference string(name of object) to the actual object.
        #this is needed in order to build 'extended objects'
        refList[name] = obj
