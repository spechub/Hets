while [ ! -e /tmp/exportml_done ]
 do
   sleep 0.1
done
echo "------------------------------ Creating Checkpoint"
imageTools/dmtcp/bin/dmtcp_command --quiet --bcheckpoint
echo "----------------------------- Moving Checkpoint"
ls ckpt_ocamlrun_* | xargs -I{} mv {} hol_light.dmtcp
rm dmtcp_restart_script*.sh
echo "------------------------------ Killing Process & Quitting Coordinator"
imageTools/dmtcp/bin/dmtcp_command --quiet --quit
