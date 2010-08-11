{- |
Module      :  $Id$
Description :  testing HasCASL homogeneously
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

test some parsers (and printers)
-}

module Main where

import Common.AnnoState
import Common.DocUtils
import Common.GlobalAnnotations
import Common.RunParsers

import HasCASL.HToken
import HasCASL.Builtin
import HasCASL.ParseItem
import HasCASL.ParseTerm
import HasCASL.RunMixfixParser
import HasCASL.RunStaticAna

main :: IO ()
main = exec lineParser fileParser

toHStringParser :: Pretty a => (GlobalAnnos -> AParser () a)
               -> StringParser
toHStringParser p ga = let newGa = addBuiltins ga in
    fmap (\ a -> showGlobalDoc newGa a "") $ p newGa

fromHAParser :: Pretty a => AParser () a -> StringParser
fromHAParser p ga = fmap (\ a -> showGlobalDoc (addBuiltins ga) a "") p

lineParser, fileParser :: [(String, StringParser)]
lineParser = [
 ("MixIds", fromAParser opId),
 ("Kinds", fromAParser kind),
 ("Types", fromAParser parseType),
 ("Terms", fromAParser term),
 ("MixfixTerms", toHStringParser resolveTerm),
 ("Typepattern", fromAParser typePattern),
 ("Pattern", fromHAParser pattern),
 ("BasicItems", fromHAParser basicItems),
 ("Items", fromHAParser basicSpec)]

fileParser = [ ("BasicSpec", fromHAParser basicSpec)
             , ("analysis", anaParser)
             , ("sentences", printSen senParser)
             , ("translate", printSen transParser)
             ]
