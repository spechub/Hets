include package.conf

SUBDIRS	= ac-macros src

EXTRA_DIST = VERSION configure.in.src genconf.sh \
             package.conf reconf $(PACKAGE)-$(VERSION).pkg

# Generation of a package defintion file from the package.conf file. This
# file in combination with autobundle enables integration of the package
# source tree with other software packages. See the online package base
# (www.program-transformation.org/package-base) for more information and
# available packages.
$(PACKAGE)-$(VERSION).pkg: package.conf
	@( \
	   echo "package" ;\
	   echo "identification" ;\
	   echo "  name=$(name)" ;\
	   echo "  version=$(version)" ;\
	   echo "  location=$(location)" ;\
	   echo "  info=$(info)" ;\
	   echo "  description='$(description)'" ;\
	   echo "  keywords=$(keywords)" ;\
	   echo "" ;\
           echo "interface" ;\
           echo $(patsubst %",%\n", $(interface)) | sed 's/"//g;s/^ */  /g' ;\
           echo "requires" ;\
           echo $(patsubst %",%\n", $(requires)) | sed 's/"//g;s/^ */  /g' ;\
       ) > $@
