#!/usr/bin/python
################################################################################
# Module          $Hets - FreeCAD$
#Description      Reader for the XML file dumped by Hets for FreeCAD datatypes
#Copyright        (c) Robert Savu and Uni Bremen 2011
#License          GPLv2 or higher, see LICENSE.txt
#
#Maintainer       Robert.Savu@dfki.de
#Stability        experimental
#Portability      portable
#
################################################################################

import sys
from xml.etree import ElementTree as ET

def main(argv):
    try:
        f = open (sys.argv[1], 'r')
    except IOError as (errno, strerror):
        print "I/O error({0}): {1}".format(errno, strerror)
        sys.exit(2)
    else:
        s = f.read()
        f.close()
    fcdoc = ET.XML(s)
    print fcdoc.tag
    for fcobj in fcdoc:
        print fcobj.tag
        print fcobj.attrib
        for props in fcobj:
            if props.tag == 'placement':
                a = props.attrib
            else:
                objtype = props.tag
                b = props.attrib
        print a
        print objtype
        print b
    
    

if __name__ == "__main__":
    main(sys.argv[1:])
