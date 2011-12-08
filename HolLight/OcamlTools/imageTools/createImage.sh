rm -f /tmp/exportml_done
imageTools/dmtcp/bin/dmtcp_coordinator --background
imageTools/makeCheckpoint.sh &
imageTools/dmtcp/bin/dmtcp_checkpoint --quiet ocaml -w a -init exportTools/export.ml
