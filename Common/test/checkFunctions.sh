#!/bin/sh

getNumberOfLines ()
{
   wc -l $1 | tr -s " " | cut -d " " -f1,2 | tr -d -c [0-9]
}

#parameters: progr option annofile infile outfile set?
runcheck () 
{   
    prog=$1  # takes an option and an annofile on the command line
    option=$2
    annofile=$3
    infile=$4
    outfile=$5
    set=$6
    echo "testing $option"
    if [ -x $prog ] && [ -f $annofile ] && [ -f $infile ]
    then 
	$prog $option $annofile < $infile > temp
        a=`fgrep -c -i "error" temp`
        if [ -f $outfile ]
	then
	    if diff temp $outfile > /dev/null 
	    then echo " passed"
            else 
		echo " failed diff with $outfile"
		if [ "$set" = "set" ] 
		    then cat temp > $outfile
		fi
		b=`getNumberOfLines $infile`
		if [ "$a" -ne 0 -a "$a" -ne "$b" ]
		    then echo " $a errors for $b input lines"
		fi 
	    fi	
        else 
	    echo " missing comparison file $outfile (newly created)" 
            cat temp > $outfile
	fi
    else 
        echo " missing file $prog, $annofile, or $infile"
    fi
}

runchecker ()
{
   runcheck $PA $1 $ANNOS $2 $3 $SET
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
