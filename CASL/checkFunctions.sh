#!/usr/local/bin/bash

getFirstDigits ()
{
   wc -l $1 |expand|tr -s " " | cut -d " " -f1,2 | tr -d -c [0-9]
}

#parameters: progr option infile outfile set?
runcheck () 
{   
    echo "testing $2"
    if [ -x $1 ] && [ -f $3 ]
    then 
	$1 $2 $3 >& temp
        declare -i a=`fgrep -c "parse error" temp`
        if [ -f $4 ]
	then
	    diff -w temp $4 >& /dev/null
	    if [ $? ]
	    then echo " passed"
            else echo " failed diff with $4"
	    fi
	    if [ "$5" = "set" ] 
	    then cat temp > $4
	    fi
	    declare -i b=`getFirstDigits $3`
            if [ "$a" -ne 0 -a "$a" -ne "$b" ]
            then echo " $a errors for $b input lines"
 	    fi 
	fi
    fi
}

#parameters: progr option extension set?
runmycheck ()
{
   runcheck $1 $2 $2.$3 $2.$3.output $4
} 

runwrongcheck ()
{
   runcheck $1 $2 Wrong$2.$3 Wrong$2.$3.output $4
} 

