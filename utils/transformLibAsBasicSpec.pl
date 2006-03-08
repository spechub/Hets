## This perl script gets one argument:
# a file name of a CASL library file with special markup
###
# It prints the result to stdout.
# - the processing starts in line: %[--%% Basic Spec Begin %%--]%
# - the processing ends in line: %[--%% Basic Spec End %%--]%
# - lines beginning with "then","spec","and" and "end" are skipped
#   
use strict;

open(BAS_SPEC,"< $ARGV[0]") or die "cannot read basic spec file $ARGV[0]";

my $basic_spec = "";
my $collectMode = 0;
# read basic spec
while(<BAS_SPEC>) {
    next if m/^end|spec|then|and/o;
    $collectMode=1,next if(m/%\[--%% Basic Spec Begin %%--\]%/o);
    $collectMode=0,next if(m/%\[--%% Basic Spec End %%--\]%/o);
    $basic_spec .= $_ if $collectMode;
}

print $basic_spec,"\n";
