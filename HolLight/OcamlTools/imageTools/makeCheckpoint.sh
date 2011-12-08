while [ ! -e /tmp/exportml_done ]
 do
   sleep 0.1
done
echo "------------------------------ Creating Checkpoint"
imageTools/dmtcp/bin/dmtcp_command --quiet --bcheckpoint
echo "----------------------------- Moving Checkpoint"
DISTR=`cat /etc/*-release | grep DISTRIB_RELEASE | cut -d= -f2`
ARCH=`uname -m`
mv -f ckpt_ocamlrun_* hol_light_$DISTR\_$ARCH.dmtcp
rm -f dmtcp_restart_script*.sh
echo "------------------------------ Killing Process & Quitting Coordinator"
imageTools/dmtcp/bin/dmtcp_command --quiet --quit
