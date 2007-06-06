
# every word which is matched literally in the rules section is in the 
# output list
use strict;

my $rules = 0;
my @words = ();

while(<>) {
    $rules=1,next if m/^%%$/o;
    last if $rules == 1 && m/^%%$/o;
    if ($rules ==1 && $_ =~ m,^([a-z][^ \t]+),o) {
	push @words, split(/\|/,$1);
    }    
}

my @chr = split(//,join(" ",@words));
my @out = ();

my $cnt = 0;

foreach my $elem (@chr) {
    $cnt++; 
    if ($cnt >= 55 && $cnt <= 70) {
	if ($elem =~ m,^ $,o) {
	    $cnt=0;
	    $elem=" \n";
	}
     }
    push @out,$elem;
}


print "     (\"",join("\"++\n      \"",split("\n",join("",@out))),
    "\"\n     )\n";
