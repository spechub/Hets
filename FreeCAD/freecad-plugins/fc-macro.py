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
import sys
sys.path.append('/usr/lib/freecad/lib')
import FreeCAD
import math
import Draft
import Part
from xml.etree import ElementTree as ET

App.newDocument('fromHets')

def fromHets(filePath):
    try:
        f = open (filePath, 'r')
    except IOError as (errno, strerror):
        print "I/O error({0}): {1}".format(errno, strerror)
        return 2
    else:
        s = f.read()
        f.close()
    fcdoc = ET.XML(s)
    print fcdoc.tag
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
        entity = name, placexml, attribsxml, 0
        buildque.append(entity)

    while buildque.len() > 0 :
        for elsrc in buildque:
            if isBuildable(elsrc, objtype, buildque):
                buildObject(elsrc, objtype, buildque, objDict)


#checks whether the object is buildable in the current state of the program
def isBuildable(el, ot, queue):
    name, pos, att, tr = el
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
def buildObject(el, ot, queue, refList): 
    #expand and extract elements needed for object construction
    name, pos, att, tr = el
    queue.remove(el)
    objtype = ot
    
    #build the placement from the vector and quaternion stored in the xml file
    base = FreeCAD.Vector(float(pos['x']), float(pos['y']), float(pos['z']))
    quat = [float(pos['q0']), float(pos['q1']), float(pos['q2']), float(pos['q3'])]
    q0, q1, q2, q3 = quat
    angle = 2*acos(q3)
    axis = FreeCAD.Vector(q0, q1, q2)
    place = FreeCAD.Placement(base, axis, angle)
    
    #handler to determine which object constructor to call
    if objtype == 'box':
        isCreated = False
        part = Part.makeBox(float(b[length]), float(b[width]), float(b[height]))
    elif objtype == 'cylinder':
        isCreated = False
        part = Part.makeCylinder(float(b['radius']), float(b['height']), 
        [defpnt, defdir, float(b['angle'])])
    elif objtype == 'cone':
        isCreated = False
        part = Part.makeCone(float(b['radius1']), float(b['radius2']), float(b['height']),
        [defpnt, defdir, float(b['angle'])])
    elif objtype == 'sphere':
        isCreated = False
        part = Part.makeSphere(float(b['radius']),
        [defpnt, defdir, float(b['angle1']),float(b['angle2']),float(b['angle3'])])
    elif objtype == 'torus':
        isCreated = False
        part = Part.makeTorus(float(b['radius1']), float(b['radius2']), 
        [defpnt, defdir, float(b['angle1']),float(b['angle2']),float(b['angle3'])])
    elif objtype == 'line':
        isCreated = False
        secpnt = FreeCAD.Vector(float(b['length']),0,0)
        part = Part.makeLine(defpnt, secpnt)
    elif objtype == 'circle':
        isCreated = False
        part = Part.makeCircle(float(b['radius']), [defpnt, defdir, float(b['angle1']), float(b['angle2'])])
    elif objtype == 'cut':
        isCreated = True
        obj = cut(refList[att['base']],refList[att['tool']])
    elif objtype == 'common':
        isCreated = True
        obj = fuse(refList[att['base']],refList[att['tool']])
    elif objtype == 'extrude':
        isCreated = True
        obj = extrude(refList[att['base']],float(refList[att['tool']]))
    elif objtype == 'rectangle':
        isCreated = True
        obj = makeRectangle(b['length'], b['height'],FreeCAD.Placement(),False)


    #build an empty object
    if not isCreated:
        obj = FreeCAD.ActiveDocument.addObject("Part::Feature", name)
    else:
        obj.Label = name
    
    #all objects are created with the default placement
    #now the actual placement is added to the FreeCAD object
    obj.Placement = place
        
        
    #add the mapping from the reference string(name of object) to the actual object.
    #this is needed in order to build 'extended objects'
    refList[name] = obj
