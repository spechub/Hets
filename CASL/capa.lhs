#!/home/maeder/bin/runhugs

HetCATS/CASL/capa.lhs
$Id$
Authors: Christian Maeder
Year:    2002
   
test some parsers (and printers)

\begin{code}

module Main where

import CASL.Formula
import CASL.Print_AS_Basic
import CASL.Parse_AS_Basic
import Common.RunParsers
import CASL.RunMixfixParser
import CASL.RunStaticAna

main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, StringParser)]
lineParser = [
 ("Terms", fromAParser term),
 ("Formula", fromAParser formula),
 ("SortItem", fromAParser sortItems),
 ("OpItem", fromAParser opItems),
 ("PredItem", fromAParser predItems),
 ("MixfixTerms", toStringParser resolveTerm),
 ("MixfixFormula", toStringParser resolveForm),
 ("ShowTerms", fromAParser testTerm),
 ("ShowTermsMix", toStringParser testTermMix),
 ("ShowForm", fromAParser testFormula),
 ("ShowFormMix", toStringParser testFormulaMix)]

fileParser = [("BasicSpec", fromAParser basicSpec)
	      , ("analysis", toStringParser runAna)
	     ]

\end{code}
