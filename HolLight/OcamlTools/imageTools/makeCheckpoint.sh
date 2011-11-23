while [ ! -e /tmp/exportml_done ]
 do
   sleep 1
done
imageTools/dmtcp/bin/dmtcp_command --checkpoint
imageTools/dmtcp/bin/dmtcp_command --kill
