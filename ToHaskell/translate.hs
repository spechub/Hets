module Main where

import HasCASL.ParseItem
import Haskell.Hatchet.HsPretty as HP
import Haskell.Hatchet.HsSyn
import ToHaskell.Translate
import ToHaskell.TranslateId

import Common.AnnoState
import Common.Token
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import Common.RunParsers

-- | Function for the test of the translation of identifiers.
idToHaskell :: AParser WrapString
idToHaskell = fmap (WrapString . translateId) $ parseId []

hParser :: AParser HsModule
hParser = do b <- basicSpec
	     return $ translate b

instance PrettyPrint HsModule where
    printText0 _ m = text $ HP.render $ ppHsModule m
	  
main :: IO ()
main = exec lineParser fileParser

lineParser, fileParser :: [(String, StringParser)]
lineParser = [
	      ("TranslateIds", fromAParser idToHaskell)
	     ]

fileParser = [
	      ("BasicSpec", fromAParser hParser)
	     ]
