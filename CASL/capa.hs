{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
test some parsers (and printers)
-}

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
	      , ("signature", toStringParser getSign)
	      , ("sentences", toStringParser getProps)
	     ]
