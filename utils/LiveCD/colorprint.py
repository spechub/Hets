################################################################################
# Prints colored messages.
#
# Author: Thiemo Wiedemeyer
# E-Mail: raider@informatik.uni-bremen.de
################################################################################

import sys

red    = "[31;1m"
green  = "[32;1m"
yellow = "[33;1m"
blue   = "[34;1m"
black  = "[0m"

##
# Prints a message in a given color to the console.
# @param info Message string.
# @param color Color string.
def printColor(info, color):
	if sys.stdout.isatty():
		print "%s%s%s" % (color, info, black)
	else:
		print info
	return

##
# Prints a startmessage (green).
# @param info Message string.
def printStart(info):
	printColor(info, green)
	return

##
# Prints an infomessage (blue).
# @param info Message string.
def printInfo(info):
	printColor(info, blue)
	return

##
# Prints an exitmessage (yellow) or an errormessage (red) if ret != 0.
# @param info Message string.
# @param ret Returnvalue of function.
def printExit(info, ret):
	if ret == 0:
		printColor(info, yellow)
	else:
		printColor("... error!", red)
	return

