for f in ./examples/*.isa
do
	cat $f | tidy -utf8 -xml -w 255 -i -c -q -asxml > "${f}.pretty.xml"
done
