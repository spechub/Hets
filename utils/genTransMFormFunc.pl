# $Id$
# usage:
#   genInlines.pl Modal/GeneratePatterns.inline.hs.in Modal/ModalSystems.hs

# substitute ##<WORD> with Haskell code snippits

use strict;
use File::Basename;

# subtitutions with common parts of Modal- and CASL-formulas
my %substs =
 ("�!modalAx" =>
  "inlineAxioms Modal \"modality empty\\n".
"pred p,q:()\\n".
". ",
  "�!caslAx" =>
  "inlineAxioms CASL \"sort world\\n".
"pred rel : world * world\\n".
"forall w1 : world\\n. ");

my $input = "";

my ($infile,$outfile) = @ARGV;

# Argument processing
###unless ($infile eq "DEBUG") {
die "exactly one in- and one out-file needed!!" unless @ARGV == 2;

my $outfile1 = join "", (fileparse($infile,'\.in'))[1,0];

print STDERR "Generating $outfile1\n";

# open the first two files
open IN, "<$infile" or die "cannot read \"$infile\"";
open OUT, ">$outfile1" or die "cannot write to \"$outfile1\"";

# perform the substitutions
while (<IN>) {
   foreach my $key (keys %substs) {
      s/$key\"/$substs{$key}/ge;
   }
   print OUT $_;
}

close IN;
close OUT;

# call outlineAxioms and get the result imidiately
$input = `utils/outlineAxioms $outfile1`;
if($? >> 8) {
    print STDERR "outlineAxioms detected an error\n";
    exit 5;
}
###}
###if ($input eq "") {
###   $input = join("",<STDIN>);
###}

# process the output of outlineAxioms (further called input)
$input =~ s,^.*snip\s+><\s+Patterns(.*)snip\s+>/<\s+Patterns,$1,s;
$input =~ s/^\s*\[\(\[\[//s;
$input =~ s/(\})\]\]\)\]\s*$/$1/s;

# print "$input\n";
# split the input into pairs
my @input = split(/\]\]\),\s+?\(\[\[/s, $input);

print STDERR "Generating $outfile\n";

# open the outputfile and print out the header
open OUT, ">$outfile" or die "cannot write to \"$outfile\"";

print OUT '{- look but don\'t touch !!
generated by utils genTransMFormFunc.pl -}

module Modal.ModalSystems (transSchemaMFormula) where

import Common.DocUtils
import Common.AS_Annotation
import Common.Id

-- CASL
import CASL.AS_Basic_CASL

-- ModalCASL
import Modal.AS_Modal
import Modal.Print_AS ()
import Modal.Utils

transSchemaMFormula :: ([VAR] -> TERM M_FORMULA -> TERM ())
                    -> SORT -> PRED_NAME -> [VAR]
                    -> AnModFORM -> Maybe (Named CASLFORMULA)

',
'transSchemaMFormula mapT world rel vars anMF =
   let '.
          join("\n       ",map {'w'.$_.' = vars !! '.($_-1);} (1,2,3)).
          ' in
    case (getRLabel anMF,item anMF) of
';

foreach my $pair (@input) {
#    print "Pair: $pair\n";
    my $moda_i = 0;
    # split each pair into raw pattern and raw result
    my ($pattern,$result) = split /\]\],\s+?\[\[/s,$pair;
    #print STDERR "    $pattern => $result\n";
    # pattern is the left hand side of the case '->'
    # Each field of NamedSen is substituted by a variable
    # And then NamedSen is transformend to a tuple
    $pattern =~ s/""/_label/os;
    # remove line breaks and spaces
    $pattern =~ s/\n//gos;
    $pattern =~ s/\s+/ /go;
    # add variables foreach modality
    $pattern =~ s/Simple_mod empty/'moda'.$moda_i++/goe;
    # substitute formula variables with underscore
    # only 'p','q' and 'r' are recognized
    $pattern =~ s/ [pqr] / _ /go;
    # substitute nullRange with underscore
    $pattern =~ s/nullRange/ _ /go;
    # remove all stuff that s not needed from the pattern
    # closing brace
    $pattern =~ s/\}\s*$//o;
    # SenAttr Constructor, opening brace and first selector
    $pattern =~ s/SenAttr\{senAttr = //o;
    #print STDERR "222: $pattern\n";
    # new isAxiom field
    $pattern =~ s/isAxiom = \w+,//o;
    # new isDef field
    $pattern =~ s/isDef = \w+,//o;
    # new wasTheorem field
    $pattern =~ s/wasTheorem = \w+,//o;
    # new simpAnno field
    $pattern =~ s/simpAnno = \w+,//o;
    # new attrOrigin field
    $pattern =~ s/attrOrigin = \w+,//o;
    # sentence selector
    $pattern =~ s/ sentence = //o;
    #print STDERR "223: $pattern\n";
    # All empty lists in the pattern are substituted by underscores
    $pattern =~ s/\[\]/_/go;
    # the result is in the right format and only white spaces / line
    # breaks are removed
    $result =~ s/\n//gos;
    $result =~ s/\s+/ /go;
    my $list = "";
    for (my $i = 0; $i < $moda_i; $list .= 'moda'.$i++.",") {};
    $list = "[$list";
    $list =~ s/,$/]/o;
    unless ($result =~ m/^\s*Nothing\s*$/o) {
        $result = "Just \$ ".$result;
    }
    print OUT
'      ('.$pattern.") ->\n".
'         addTerm mapT rel (map modToTerm '.$list.') vars ('.$result.")\n";
}
print OUT
'      (_,f)'." ->\n".
'          error ("Modal2CASL: unknown formula: " ++ showDoc f "") Nothing
';

close OUT;
