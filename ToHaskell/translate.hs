module Main where

import HasCASL.ParseItem
import Haskell.Language.Pretty
import Haskell.Language.Syntax
import ToHaskell.Translate
import ToHaskell.TranslateAna

import Common.AnnoState
import Common.Lib.Parsec
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.RunParsers

hParser :: AParser HsModule
hParser = do b <- basicSpec
	     return $ translate b

instance PrettyPrint HsModule where
    printText0 _ m = text $ prettyPrint m
	  
main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, StringParser)]
lineParser = [
	      ("TranslateIds", fromAParser idToHaskell)
	     ]

fileParser = [
	      ("BasicSpec", fromAParser hParser)
	     ]
