{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

test some parsers (and printers)
-}

module Main where

import HasCASL.ParseItem
import HasCASL.ParseTerm
import HasCASL.HToken
import Common.RunParsers
import HasCASL.RunMixfixParser
import HasCASL.RunStaticAna

main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, StringParser)]
lineParser = [
 ("MixIds", fromAParser uninstOpId),
 ("Kinds", fromAParser kind),
 ("Types", fromAParser parseType),
 ("Terms", fromAParser term),
 ("MixfixTerms", toMyStringParser resolveTerm),
 ("Typepattern", fromAParser typePattern),
 ("Pattern", fromAParser pattern),
 ("BasicItems", fromAParser basicItems),
 ("Items", fromAParser basicSpec)]

fileParser = [ ("BasicSpec", fromAParser basicSpec)
             , ("analysis", anaParser)
             , ("sentences", printSen senParser)
             , ("translate", printSen transParser)
             ]

