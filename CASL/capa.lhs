#!/home/maeder/bin/runhugs

HetCATS/CASL/capa.lhs
$Id$
Authors: Christian Maeder
Year:    2002
   
test some parsers (and printers)

\begin{code}

module Main where

import Common.Token
import CASL.Formula
import CASL.Print_AS_Basic
import CASL.Parse_AS_Basic
import CASL.SortItem
import CASL.OpItem
import CASL.RunParsers
import CASL.RunMixfixParser
import CASL.RunStaticAna
import ToHaskell.TranslateAna

main :: IO ()
main = exec lineParser fileParser
    where _just_avoid_unused_import_warning = pluralS_symb_list

lineParser, fileParser :: [(String, HetParser)]
lineParser = [
 ("MixIds", HetParser parseId),
 ("TranslateIds", HetParser idToHaskell),
 ("Terms", HetParser term),
 ("Formula", HetParser formula),
 ("SortItem", HetParser sortItems),
 ("OpItem", HetParser opItems),
 ("PredItem", HetParser predItems),
 ("MixfixTerms", HetParser resolveTerm),
 ("MixfixFormula", HetParser resolveForm),
 ("VarIds", HetParser varId),
 ("ShowTerms", HetParser testTerm),
 ("ShowTermsMix", HetParser testTermMix),
 ("ShowForm", HetParser testFormula),
 ("ShowFormMix", HetParser testFormulaMix)]

fileParser = [("BasicSpec", HetParser basicSpec)
	      , ("analysis", HetParser runAna)
	     ]

\end{code}
