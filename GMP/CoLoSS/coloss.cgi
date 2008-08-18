#!/bin/sh
LD_LIBRARY_PATH=/home/cofi/www/CoLoSS/missingSO
export LD_LIBRARY_PATH
/home/cofi/www/CoLoSS/data/timeout 120 /home/cofi/www/CoLoSS/data/main "$@"
