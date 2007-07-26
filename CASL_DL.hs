{- |

The CASL_DL folder contains the CASL_DL (see
<http://www.informatik.uni-bremen.de/~luettich/papers/owl-casl-dl.pdf>) 
instance of "Logic.Logic".  All the
data for this instance is assembled in "CASL_DL.Logic_CASL_DL".

Note that the data structures reuse the AbstractSyntax of "CASL" where it 
provides /holes/.

/Abstract Syntax/

The additional abstract syntax of CASL_DL basic specifications 
is provided in
"CASL_DL.AS_CASL_DL" as a Haskell algebraic datatype. 

/Parser/

The additional CASL_DL parser, 
written with <http://www.cs.uu.nl/people/daan/parsec.html>, 
is contained in
"CASL_DL.Parse_AS". 

/Printing/

 Pretty printing (based on "Common.Lib.Pretty")
of CASL_DL basic specifications is provided in
"CASL_DL.Print_AS". Pretty printing of signature elements is provided in 
"CASL_DL.Sign".

/Signatures/

The data structures for CASL signatures are contained in "CASL_DL.Sign".
CASL_DL sentences are
represented as abstract syntax trees of type
'CASL.AS_Basic_CASL.FORMULA' filled with 'CASL_DL.AS_CASL_DL.DL_FORMULA'.  
In order to understand these data
structures, you also should have a look at some of the "Common"
modules, providing data structures for identifiers ("Common.Id"), sets
("Common.Lib.Set"), maps ("Common.Lib.Map") and relations
("Common.Lib.Rel").

/Static Analysis/

The main module for static analysis of CASL_DL basic specifications is
"CASL_DL.StatAna". The outcome basically is a signature and a set of
sentences.  It wraps the CASL static analysis in a specific way. 
"CASL.Overload", "CASL.Inject" and "CASL.Project" deal
with subsorting.

/Predefined Datatypes/

"CASL_DL.PredefinedDatatypes" is generated from some CASL datatypes 
defined in CASL_DL\/Datatypes.het.

-}

module CASL_DL where
