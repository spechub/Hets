
{- HetCATS/CASL/Main.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   test some parsers (and printers)
-}

module Main where

import Token
import Formula
import Print_AS_Basic()
import Parse_AS_Basic
import SortItem
import OpItem
import RunParsers

main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, HetParser)]
lineParser = [
 ("MixIds", HetParser parseId),
 ("Terms", HetParser term),
 ("Formula", HetParser formula),
 ("SortItem", HetParser sortItems),
 ("OpItem", HetParser opItems),
 ("PredItem", HetParser predItems)]

fileParser = [("BasicSpec", HetParser basicSpec)]
