SHELL=/bin/bash

hol_light.dmtcp: Makefile exportTools/*.ml imageTools/*.sh
	echo ${PWD}
	rm -f /tmp/exportml_done
	imageTools/makeCheckpoint.sh

clean:
	rm -rf *.dmtcp
