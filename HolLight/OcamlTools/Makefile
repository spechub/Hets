SHELL=/bin/bash
PLATFORM=`uname -m`
DMTCP_VERSION="1.2.3"
HETS_HOLLIGHT_TOOLS=$(PWD)/exportTools/

hol_light.dmtcp: Makefile exportTools/*.ml imageTools/*.sh imageTools/hol_light/pa_j.ml imageTools/dmtcp/bin/dmtcp_command imageTools/dmtcp/bin/dmtcp_coordinator imageTools/dmtcp/bin/dmtcp_checkpoint
	HETS_OCAML_LIB_DIR=${HETS_OCAML_LIB_DIR} \
HETS_HOL_DIR=${HETS_HOL_DIR} \
HETS_HOLLIGHT_TOOLS=${HETS_HOLLIGHT_TOOLS} \
imageTools/createImage.sh

clean:
	rm -rf *.dmtcp imageTools/dmtcp/ imageTools/hol_light/ imageTools/tmp/*

imageTools/hol_light/pa_j.ml: imageTools/hol_light/
	make -C imageTools/hol_light/ && touch imageTools/hol_light/pa_j.ml

imageTools/hol_light/: imageTools/tmp/hol_light.tar.gz
	cd imageTools/tmp/ && tar zfx hol_light.tar.gz && mv hol_light ../

imageTools/tmp/hol_light.tar.gz:
	wget http://www.cl.cam.ac.uk/~jrh13/hol-light/hol_light_100110.tgz -O imageTools/tmp/hol_light.tar.gz

imageTools/dmtcp/bin/dmtcp_%: imageTools/dmtcp/bin/
	:

imageTools/dmtcp/bin/: imageTools/dmtcp/
	cd imageTools/dmtcp && ./configure && make

imageTools/dmtcp/: imageTools/tmp/dmtcp.tar.gz
	cd imageTools/tmp/ && tar xzf dmtcp.tar.gz && mv dmtcp-$(DMTCP_VERSION) ../dmtcp

imageTools/tmp/dmtcp.tar.gz:
	wget http://downloads.sourceforge.net/project/dmtcp/dmtcp/$(DMTCP_VERSION)/dmtcp-$(DMTCP_VERSION).tar.gz -O imageTools/tmp/dmtcp.tar.gz
