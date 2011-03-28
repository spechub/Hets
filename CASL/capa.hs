{- |
Module      :  $Id$
Description :  testing mere CASL basic specs
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

test some parsers (and printers)
-}

module Main where

import CASL.Formula
import CASL.AS_Basic_CASL
import CASL.ToDoc ()
import CASL.Parse_AS_Basic
import Common.AnnoState
import Common.RunParsers
import CASL.RunMixfixParser
import CASL.RunStaticAna

main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, StringParser)]
lineParser = [
 ("Terms", fromAParser (term [] :: AParser () (TERM ()))),
 ("Formula", fromAParser (formula [] :: AParser () (FORMULA ()))),
 ("SortItem", fromAParser (sortItems [] :: AParser () (SIG_ITEMS () ()))),
 ("OpItem", fromAParser (opItems [] :: AParser () (SIG_ITEMS () ()))),
 ("PredItem", fromAParser (predItems [] :: AParser () (SIG_ITEMS () ()))),
 ("MixfixTerms", toStringParser resolveTerm),
 ("MixfixFormula", toStringParser resolveForm),
 ("ShowTerms", fromAParser testTerm),
 ("ShowTermsMix", toStringParser testTermMix),
 ("ShowForm", fromAParser testFormula),
 ("ShowFormMix", toStringParser testFormulaMix)]

fileParser = [("BasicSpec", fromAParser (basicSpec []
                                         :: AParser () (BASIC_SPEC () () ())))
              , ("analysis", toStringParser runAna)
              , ("signature", toStringParser getSign)
              , ("sentences", toStringParser getProps)
             ]
