#!/usr/local/bin/bash

getFirstDigits ()
{
   wc -l $1 |expand|tr -s " " | cut -d " " -f1,2 | tr -d -c [0-9]
}

#parameters: progr infile outfile set?
runcheck () 
{   
    echo "testing $2"
    if [ -f $2 ]
    then 
	$1 $2 > temp
        declare -i a=`fgrep -c -i "error" temp`
        if [ -f $3 ]
	then
	    if diff temp $3 >& /dev/null 
	    then echo " passed"
            else 
		echo " failed diff with $3"
		if [ "$4" = "set" ] 
		    then cat temp > $3
		fi
		declare -i b=`getFirstDigits $2`
		if [ "$a" -ne 0 -a "$a" -ne "$b" ]
		    then echo " $a errors for $b input lines"
		fi 
	    fi	
        else 
	    echo " missing comparison file $3 (newly created)" 
            cat temp > $3
	fi
    else 
	echo " missing file $2"
    fi
}

runchecker ()
{
   runcheck $PA $1 $2 $SET
}

#parameters: option extension
runmycheck ()
{
   runchecker $1 $1.output $SET
} 


