rm /tmp/exportml_done
imageTools/dmtcp/bin/dmtcp_coordinator --background
imageTools/dmtcp/bin/dmtcp_checkpoint ocaml exportTools/export.ml
