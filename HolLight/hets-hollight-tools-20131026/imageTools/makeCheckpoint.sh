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
