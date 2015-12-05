SHELL=/bin/bash
HETS_HOLLIGHT_TOOLS=$(PWD)/exportTools/

hol_light.dmtcp: Makefile exportTools/*.ml imageTools/*.sh
	rm -f /tmp/exportml_done
	HETS_HOL_DIR="/usr/share/hol-light/" \
HETS_HOLLIGHT_TOOLS=${HETS_HOLLIGHT_TOOLS} \
/bin/bash imageTools/createImage.sh &
	HETS_HOL_DIR="/usr/share/hol-light/" \
HETS_HOLLIGHT_TOOLS=${HETS_HOLLIGHT_TOOLS} \
/bin/bash imageTools/makeCheckpoint.sh

clean:
	rm -rf *.dmtcp
