#!/usr/bin/python
################################################################################
# Creates a LiveCD for Hets.
# Uses the morphix-tools to create/modify LiveCDs easily. Because morphix-tools
# depends on a Debian-Based distributions this program just works such systems.
#
# Author: Thiemo Wiedemeyer
# E-Mail: raider@informatik.uni-bremen.de
################################################################################

import sys, os, re
from colorprint import printStart, printInfo, printExit

rootpath = r"./"
execpath = rootpath+r"exec/"
mainpath = rootpath+r"main/"
minipath = rootpath+r"mini/"
copypath = rootpath+r"copy/"
temppath = rootpath+r"temp/"
tmpfile1 = temppath+r"tmp1.iso"
tmpfile2 = temppath+r"tmp2.iso"
isofile  = rootpath+r"HetsLiveCD.iso"
modfile  = mainpath+r"hets.mod"
xmlfile  = rootpath+r"HetsLiveCD.xml"
datafile = copypath+r"hetsdata.tbz2"

##
# Invocates 'mv' to move a file from source to dest.
# @param source Source path of the file.
# @param dest   Destination path of the file.
# @return       Returnvalue of 'mv'.
def moveFile(source, dest):
	printStart("Moving file...")

	cmd = "mv %s %s" % (source, dest)
	printInfo(cmd)
	ret = os.system(cmd)

	printExit("... file moved!", ret)
	return ret

##
# Invocates 'mmaker' to create a MainMod out of the HetsLiveCD.xml.
# @return Returnvalue of 'mmaker'.
def createMainMod():
	printStart("Creating main mod...")

	cmd = "mmaker -v %s %s" % (xmlfile, modfile)
	printInfo(cmd)
	ret = os.system(cmd)

	printExit("... main mod created!", ret)
	return ret

##
# Invocates 'morphmini' to create MiniMods out of each *Mini.xml file.
# @return Returnvalue of 'morphmini'.
def createMiniMods():
	printStart("Creating mini mods...")
	reg = re.compile(r"^.*Mini\.xml")
	ret = 0

	for item in os.listdir(rootpath):
		file = os.path.join(rootpath, item)
		if os.path.isfile(file) or os.path.islink(file):
			if not reg.match(item):
				continue
			printInfo("creating mini mod for '%s'" % (item))
			cmd = "morphmini %s %s" % (file, minipath+item.replace("Mini.xml", ".mod"))
			printInfo(cmd)
			ret = os.system(cmd)
		if ret != 0:
			break

	printExit("... mini mods created!", ret)
	return ret

##
# Invocates 'isomorph' to delete given content from a MorpixIso file.
# @param source Source path of the iso file.
# @param dest   Destination path of the iso file.
# @param delete Name of the content that should be deleted. If 'all' all
#               content is deleted
# @return       A Tupel containing the returnvalue of 'isomorph', the new
#               source path of the iso file and the new destination path for
#               the next action.
def delContent(source, dest, delete):
	printStart("Deleting old content...")

	printInfo("\t... deleting %s" % delete)
	if delete == "all":
		cmd = "isomorph --del-all %s %s" % (source, dest)
	else:
		cmd = "isomorph --del-all %s %s %s" % (delete, source, dest)

	printInfo(cmd)
	ret = os.system(cmd)

	printExit("... old content deleted!", ret)
	source, dest = dest, source
	return ret, source, dest

##
# Invocates 'isomorph' to add the MainMod to a MorpixIso file.
# @param source Source path of the iso file.
# @param dest   Destination path of the iso file.
# @return       A Tupel containing the returnvalue of 'isomorph', the new
#               source path of the iso file and the new destination path for
#               the next action.
def addMainMod(source, dest):
	printStart("Insert main mod...")

	cmd = "isomorph --add main %s %s %s" % (modfile, source, dest)
	printInfo(cmd)
	ret = os.system(cmd)

	printExit("... main mod inserted!", ret)
	source, dest = dest, source
	return ret, source, dest

##
# Invocates 'isomorph' to add the MiniMods to a MorpixIso file.
# @param source Source path of the iso file.
# @param dest   Destination path of the iso file.
# @return       A Tupel containing the returnvalue of 'isomorph', the new
#               source path of the iso file and the new destination path for
#               the next action.
def addMiniMods(source, dest):
	printStart("Insert mini mods...")
	ret = 0

	for item in os.listdir(minipath):
		file = os.path.join(minipath, item)
		cmd = "isomorph --add mini %s %s %s" % (file, source, dest)
		printInfo("insert mini mod '%s'..." % (file))
		printInfo(cmd)
		ret = os.system(cmd)
		source, dest = dest, source
		if ret != 0:
			break

	printExit("... mini mods inserted!", ret)
	return ret, source, dest

##
# Invocates 'isomorph' to add a given file to a given destination path on the
# LiveCD to a MorpixIso file.
# @param file   Source path file that should be added.
# @param path   Destination path where the file should be added.
# @param source Source path of the iso file.
# @param dest   Destination path of the iso file.
# @return       A Tupel containing the returnvalue of 'isomorph', the new
#               source path of the iso file and the new destination path for
#               the next action.
def addFile2Copy(file, path, source, dest):
	printStart("Insert file '%s' to '%s'..." % (file, path))

	cmd = "isomorph --add copy %s %s %s %s" % (file, path, source, dest)
	printInfo(cmd)
	ret = os.system(cmd)

	printExit("... file added!", ret)
	source, dest = dest, source
	return ret, source, dest

##
# Invocates addFile2Copy for each file in the copy directory.
# @param path   Path to look for files that should be added.
# @param root   Base path where the files should be added.
# @param source Source path of the iso file.
# @param dest   Destination path of the iso file.
# @return       A Tupel containing the returnvalue of addFile2Copy, the new
#               source path of the iso file and the new destination path for
#               the next action.
def addFiles2Copy(path, root, source, dest):
	ret = 0
	for item in os.listdir(path):
		file = os.path.join(path, item)
		newpath = os.path.join(root, item)
		if os.path.isfile(file) or os.path.islink(file):
			ret, source, dest = addFile2Copy(file, root, source, dest)
		elif os.path.isdir(file):
			ret, source, dest = addFiles2Copy(file, newpath , source, dest)
		if ret != 0:
			break
	return ret, source, dest

##
# Invocates 'isomorph' to add content of the exec directory to a MorpixIso
# file.
# @param source Source path of the iso file.
# @param dest   Destination path of the iso file.
# @return       A Tupel containing the returnvalue of 'isomorph', the new
#               source path of the iso file and the new destination path for
#               the next action.
def addExec(source, dest):
	printStart("Insert exec files...")

	cmd = "isomorph --add exec %s %s %s" % (execpath+"*", source, dest)
	printInfo(cmd)
	ret = os.system(cmd)

	printExit("... exec files inserted!", ret)
	source, dest = dest, source
	return ret, source, dest

##
# Invocates 'rm' to remove all content from the given directory.
# @param dir Directory that should be cleaned.
# @return    Returnvalue of 'rm'.
def cleanDir(dir):
	printStart("Deleting files from '%s'..." % (dir))

	cmd = "rm -f %s" % (dir+"*")
	printInfo(cmd)
	ret = os.system(cmd)

	printExit("... files from '%s' deleted!" % (dir), ret)
	return ret

##
# Invocates cleanDir all directories that should be cleaned.
# @param all If True temp, main and mini directories are clened else just temp.
# @return    Returnvalue of cleanDir.
def cleanup(all=False):
	if not all:
		return cleanDir(temppath)

	for dir in (temppath, mainpath, minipath):
		if cleanDir(dir) != 0:
			return -1
	return 0

##
# Prints a usage message to the console.
#
def usage():
	print "Usage:"
	print " %s Option" % os.path.split(sys.argv[0])[1]
	print ""
	print "Options:"
	print "  [copy|exec|main|mini|clean|mkmain|mkmini|mkiso|all|deltmp|delall]"
	print ""
	print "Description:"
	print "  copy    copies files from './copy' to iso."
	print "  exec    copies files from './exec' to iso."
	print "  main    copies main module './main/hets.mod' to iso."
	print "  mini    copies all mini modules from './mini/' to iso."
	print "  clean   deletes exec, main, copy, mini from iso."
	print "  mkmain  creates the mainmod out of './HetsLiveCD.xml'."
	print "  mkmini  creates minimods for all './*Mini.xml'."
	print "  mkiso   makes a clean and adds exec, main, copy, mini to iso."
	print "  all     makes a clean, creates main and mini mods and adds exec, main, copy,"
	print "          mini to iso."
	print "  deltmp  deletes content of './temp'."
	print "  delall  deletes content of './mini', './main' and './temp'."
	return

if __name__ == "__main__":
	# Check argument count
	if len(sys.argv) != 2:
		print "Wrong parameter count."
		usage()
		sys.exit(-1)

	# Check if command is in available command list
	if not sys.argv[1] in ("copy","exec","main","mini","clean","mkmain","mkmini","mkiso","all","deltmp","delall"):
		print "Unknown command."
		usage()
		sys.exit(-4)

	# Setting source and destination iso files
	source = tmpfile1
	dest = tmpfile2

	# If command is a command that manipulates iso files, the HetsLiveCD.iso is moved to source
	if not sys.argv[1] in ("mkmain","mkmini","deltmp","delall"):
		if moveFile(isofile, source) != 0:
			sys.exit(-8)

	# copy
	if sys.argv[1] == "copy":
		ret, source, dest = delContent(source, dest, "copy")
		if ret != 0:
			sys.exit(-8)
		ret, source, dest = addFiles2Copy(copypath, "/", source, dest)
		if ret != 0:
			sys.exit(-5)

	# exec
	elif sys.argv[1] == "exec":
		ret, source, dest = delContent(source, dest, "exec")
		if ret != 0:
			sys.exit(-8)
		ret, source, dest = addExec(source, dest)
		if ret != 0:
			sys.exit(-6)

	# main
	elif sys.argv[1] == "main":
		ret, source, dest = delContent(source, dest, "main")
		if ret != 0:
			sys.exit(-8)
		ret, source, dest = addMainMod(source, dest)
		if ret != 0:
			sys.exit(-7)

	# mini
	elif sys.argv[1] == "mini":
		ret, source, dest = delContent(source, dest, "mini")
		if ret != 0:
			sys.exit(-8)
		ret, source, dest = addMiniMods(source, dest)
		if ret != 0:
			sys.exit(-11)

	# clean
	elif sys.argv[1] == "clean":
		ret, source, dest = delContent(source, dest, "all")
		if ret != 0:
			sys.exit(-8)

	# mkmain
	elif sys.argv[1] == "mkmain":
		if createMainMod() != 0:
			sys.exit(-9)
		sys.exit(0)

	# mkmini
	elif sys.argv[1] == "mkmini":
		if createMiniMods() != 0:
			sys.exit(-10)
		sys.exit(0)

	# mkiso
	elif sys.argv[1] == "mkiso":
		ret, source, dest = delContent(source, dest, "all")
		if ret != 0:
			sys.exit(-8)
		ret, source, dest = addExec(source, dest)
		if ret != 0:
			sys.exit(-6)
		ret, source, dest = addFiles2Copy(copypath, "/", source, dest)
		if ret != 0:
			sys.exit(-5)
		ret, source, dest = addMiniMods(source, dest)
		if ret != 0:
			sys.exit(-11)
		ret, source, dest = addMainMod(source, dest)
		if ret != 0:
			sys.exit(-7)

	# all
	elif sys.argv[1] == "all":
		if createMainMod() != 0:
			sys.exit(-9)
		if createMiniMods() != 0:
			sys.exit(-9)
		ret, source, dest = delContent(source, dest, "all")
		if ret != 0:
			sys.exit(-8)
		ret, source, dest = addExec(source, dest)
		if ret != 0:
			sys.exit(-6)
		ret, source, dest = addFiles2Copy(copypath, "/", source, dest)
		if ret != 0:
			sys.exit(-5)
		ret, source, dest = addMiniMods(source, dest)
		if ret != 0:
			sys.exit(-11)
		ret, source, dest = addMainMod(source, dest)
		if ret != 0:
			sys.exit(-7)

	# deltmp
	elif sys.argv[1] == "deltmp":
		if cleanup(False) != 0:
			sys.exit(-12)
		sys.exit(0)

	# delall
	elif sys.argv[1] == "delall":
		if cleanup(True) != 0:
			sys.exit(-13)
		sys.exit(0)

	if not sys.argv[1] in ("mkmain","mkmini","deltmp","delall"):
		if moveFile(source, isofile) != 0:
			sys.exit(-8)
		if cleanup(False) != 0:
			sys.exit(-12)

	sys.exit(0)
