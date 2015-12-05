dmtcp_coordinator --daemon --quiet
sleep infinity | dmtcp_checkpoint --quiet ocaml -w a -I +compiler-libs -init exportTools/export.ml
echo "------------------------------ Done running OCAML"
