#!/bin/sh -e

export HETS_HOLLIGHT_TOOLS=/usr/lib/hets/hets-hollight-tools
export HETS_HOL_DIR=/usr/share/hol-light
export HETS_OCAML_LIB_DIR=/usr/lib/ocaml/compiler-libs

rm -f /tmp/exportml_done
dmtcp_coordinator --background
(while [ ! -e /tmp/exportml_done ]
 do
   sleep 0.1
done
dmtcp_command --quiet --bcheckpoint
dmtcp_command --quiet --quit) &
dmtcp_checkpoint --quiet ocaml -w a -init $HETS_HOLLIGHT_TOOLS/export.ml

mv ckpt_ocamlrun_* hol_light.dmtcp
rm dmtcp_restart_script*.sh
