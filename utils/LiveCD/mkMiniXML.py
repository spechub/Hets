#!/usr/bin/python
################################################################################
# Creates MiniMods xml descriptions for HetsLiveCD.
# MiniMods are used to extend a MainMod. In this case they are used to map
# complete directories to the root filesystem.
#
# Author: Thiemo Wiedemeyer
# E-Mail: raider@informatik.uni-bremen.de
################################################################################

import sys, os
from colorprint import printStart, printInfo, printExit

##
# creates a MiniMod xml description with the givin name. All files and
# directories from source are mapped through the base directory dest on the
# LiveCD.
# @param name   Name of the MiniMod.
# @param source Source directory that should be mapped.
# @param dest   Base directory on the LiveCD where the source directory should
#               appear.
def createXML(name, source, dest):
	printStart("Creating mini mod xml file...")
	printInfo("opening file '%sMini.xml'..." % (name))
	xml = open("%sMini.xml" % (name), "w+")
	printInfo("writing head to file...")
	xml.write(createHead(name))

	addFiles(xml, os.path.abspath(source), dest)

	printInfo("writing tail to file...")
	xml.write(createTail())
	printInfo("closing file...")
	xml.close()
	printExit("...mini mod xml file created!",0)
	return

##
# Adds all content from source directory to the dest directory on the LiveCD.
# @param xml    Opened fileobject of the xml file.
# @param source Source directory that should be mapped.
# @param dest   Base directory on the LiveCD where the source directory should
#               appear.
def addFiles(xml, source, dest):
	printInfo("adding content from '%s'..." % (source))
	for item in os.listdir(source):
		file = os.path.join(source, item)
		if os.path.isfile(file) or os.path.islink(file):
			printInfo("adding file '%s'..." % (item))
			xml.write(addFile(file, os.path.join(dest, item)))
		elif os.path.isdir(file):
			addFiles(xml, file, os.path.join(dest, item))

##
# Return the xml string for a file mapping from source to dest.
# @param source Source path of a file that should be mapped.
# @param dest   Destination path of the mapping.
# @return       The xml string for the mapping.
def addFile(source, dest):
	return \
		"     <local>\n" +\
		"      <from>%s</from>\n" % (convertStr(source)) +\
		"      <to>%s</to>\n" % (convertStr(dest)) +\
		"     </local>\n"

##
# Return the head of the MiniMod xml file.
# @param name Name of the MiniMod.
# @return     A xml string containing the header.
def createHead(name):
	return \
		"<comps>\n" +\
		" <group>\n" +\
		"  <minimod>\n" +\
		"   <version>0.0.1</version>\n" +\
		"   <description>Created for HetsLiveCD</description>\n" +\
		"   <minitag>%s</minitag>\n" % (name) +\
		"   <maintag>ALL</maintag>\n" +\
		"   <bootoption>ALL</bootoption>\n" +\
		"   <root>\n" +\
		"    <files>\n"

##
# Return the tail of the MiniMod xml file.
# @return A xml string containing the footer.
def createTail():
	return \
		"    </files>\n" +\
		"   </root>\n" +\
		"  </minimod>\n" +\
		" </group>\n" +\
		"</comps>\n"

##
# Converts some character to the xml representation.
# @param str Sting to convert.
# @return Converted string.
def convertStr(str):
	str = str.replace("&",r"&amp;")
	str = str.replace("'",r"&apos;")
	str = str.replace("<",r"&lt;")
	str = str.replace(">",r"&gt;")
	str = str.replace("\"",r"&quot;")
	return str

##
# Prints a usage message to the console.
#
def usage():
	print "Usage:"
	print " %s name source dest" % os.path.split(sys.argv[0])[1]
	print "Options:  Description:"
	print "  name    name of the mini mod."
	print "  source  directory containing the files that should be stored in the mini mod."
	print "  dest    destination on the live cd filesystem, where the files should appear."
	return

if __name__ == "__main__":
	# Check argument count
	if len(sys.argv) != 4:
		print "Wrong parameter count."
		usage()
		sys.exit(-1)

	# Check if second argument is a valid directory
	if not os.path.isdir(sys.argv[2]):
		print "Parameter is no existing directory."
		usage()
		sys.exit(-2)

	# Start xml creation
	createXML(sys.argv[1], sys.argv[2], sys.argv[3])
	sys.exit(0)
