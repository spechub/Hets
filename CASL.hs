{- |
Module      :  $Id$
Description :  basics of the common algebraic specification language
Copyright   :  (c) Christian Maeder and DFKI Lab Bremen 2007
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable (except CASL.Logic_CASL and CASL.QuickCheck)

The "CASL" folder contains the CASL (see
<http://www.cofi.info/CASL.html>) instance of "Logic.Logic".  All the
data for this instance is assembled in "CASL.Logic_CASL".

Note that the data structures are equipped with /holes/,
represented by type variables, that can be instantiated later on.
This is needed by CASL extensions, which typically extend
abstract syntax, signatures and signature morphisms.
For CASL, these holes are just filled with the unit tpye ().
However, many pieces of code can be written for any type f
instead of (), and thus be suitable also for CASL extensions.
It may be necessary to constrain these type variables in your
code, e.g. for pretty printing prefix your types with 'Pretty f =>'.

/Abstract Syntax/

The abstract syntax of CASL basic specifications is provided in
"CASL.AS_Basic_CASL" as a Haskell algebraic datatype.  It largely
follows the CASL reference manual (see
<http://www.cofi.info/CASLDocuments.html>).  Note that the abstract
syntax of structured specifications is provided elsewhere: in the
folder /Syntax/ (see "Syntax.ADoc").

/Parser/

The CASL parser, written with <http://www.cs.uu.nl/people/daan/parsec.html>,
is contained in
"CASL.Parse_AS_Basic".  Several modules provide parsers for individual
non-terminals of the CASL grammar: "CASL.OpItem", "CASL.SortItem",
"CASL.Formula", "CASL.Quantification".  The mixfix parser (which is
called only during static analysis) is provided by
"CASL.MixfixParser".  "CASL.LiteralFuns" deals with literals (for
numbers, strings etc.).  "CASL.SymbolParser" provides parsing of symbol
maps (occurring in fitting maps or views).  Finally,
"CASL.RunMixfixParser" and "CASL.capa" provide command-line interfaces
to the parser.


/Printing/

 Pretty printing (based on "Common.Lib.Pretty")
of CASL basic specifications is provided in
"CASL.Print_AS_Basic". Auxilary modules are "CASL.ShowMixfix" (for
printing mixfix formulas and terms) and "CASL.Simplify" and
"CASL.SimplifySen" (for removing redundant type information).

"CASL.LaTeX_AS_Basic" and "CASL.LaTeX_CASL" provide LaTeX output.


/Signatures/

The data structures for CASL signatures are contained in "CASL.Sign",
those for signature morphisms in "CASL.Morphism".  CASL sentences are
represented as abstract syntax trees of type
'CASL.AS_Basic_CASL.FORMULA'.  In order to understand these data
structures, you also should have a look at some of the "Common"
modules, providing data structures for identifiers ("Common.Id"), sets
("Common.Lib.Set"), maps ("Common.Lib.Map") and relations
("Common.Lib.Rel").

 "CASL.MapSentence" implements translation of CASL sentences
along signature morphisms.

/Static Analysis/

The main module for static analysis of CASL basic specifications is
"CASL.StaticAna". The outcome basically is a signature and a set of
sentences.  "CASL.Overload", "CASL.Inject" and "CASL.Project" deal
with subsorting.

"CASL.SymbolMapAnalysis" implements analysis of symbol maps,
yielding signature morphisms.

"CASL.Amalgamability" implements amalgamability checks needed for
architectural specifications.

"CASL.RunStaticAna" is a standalone command line interface for the
static analysis.


/Consistency checking/

"CASL.CCC.OnePoint" checks for the existence of a one-point model.
"CASL.CCC.FreeTypes" checks whether a specification consists
of free datatypes and recursively defined, terminating functions.
"CASL.CCC.SignFuns" provides commonly needed analysis functions
for signatures and morphisms.


/Miscellaneous/

"CASL.Sublogic" provides data structures and analysis functions
for the CASL sublogics.

"CASL.Taxonomy" displays the subsorting graph of a CASL signature.

 "CASL.Utils" contains utilities.

"CASL.Test" seems to be obsolete.

-}

module CASL where
