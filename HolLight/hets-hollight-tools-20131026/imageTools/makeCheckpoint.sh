dmtcp_coordinator --daemon --quiet
(sleep infinity | HETS_HOL_DIR="/usr/share/hol-light/" HETS_HOLLIGHT_TOOLS="${PWD}/exportTools/" dmtcp_checkpoint --quiet ocaml -w a -I +compiler-libs -init ${PWD}/exportTools/export.ml) &
PROG_PID=$!
while [ ! -e /tmp/exportml_done ]
 do
   sleep 0.1
done
echo "------------------------------ Creating Checkpoint"
dmtcp_command --quiet --bcheckpoint
echo "----------------------------- Moving Checkpoint"
mv ckpt_ocamlrun_* hol_light.dmtcp
rm dmtcp_restart_script*.sh
echo "------------------------------ Killing Process & Quitting Coordinator"
dmtcp_command --quiet --quit
for child in $(ps -o pid --no-headers --ppid ${PROG_PID})
do
	kill $child || true
done
kill ${PROG_PID} || true
