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
	$1 $2 $3 > temp
        declare -i a=`fgrep -c -i "error" temp`
        if [ -f $4 ]
	then
	    if diff -w temp $4 >& /dev/null 
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
        else 
	    echo " missing comparison file $4 (newly created)" 
            cat temp > $4
	fi
    else 
	if [ -f $3 ] 
	then echo " missing executable $1" 
        else echo " missing file $3"
        fi
    fi
}

runchecker ()
{
   runcheck $PA $1 $2 $3 $SET
}

#parameters: option extension
runmycheck ()
{
   runchecker $1 $1.$2 $1.$2.output $SET
} 

runwrongcheck ()
{
   runchecker $1 Wrong$1.$2 Wrong$1.$2.output $SET
} 

