{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
test translation
-}

module Main where

import System.Environment

import Common.AnnoState
import Common.Lib.Parsec
import Common.Lib.State
import Common.AnnoState
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.PrettyPrint

import Haskell.Hatchet.MultiModuleBasics
import Haskell.Hatchet.HsPretty
import Haskell.Hatchet.HsSyn

import ToHaskell.TranslateAna

import HasCASL.Le
import HasCASL.AsToLe(cleanEnv, anaBasicSpec)
import HasCASL.ParseItem(basicSpec)
import Haskell.PrintModuleInfo

hParser :: AParser [HsDecl]
hParser = do b <- basicSpec
	     let env = cleanEnv $ snd $ runState 
		       (anaBasicSpec emptyGlobalAnnos b) initialEnv
		 hs = translateSig env
		 nhs = concatMap (translateSentence env) $ sentences env
	     return (cleanSig hs nhs ++ map sentence nhs)
	  
main :: IO ()
main = do l <- getArgs
	  if length l >= 1 then
	     do s <- readFile $ head l
		let r = runParser hParser emptyAnnos (head l) s 
	        case r of 
		       Right hs -> do
		           putStrLn $ showPretty emptyModuleInfo ""
			   mapM_ (putStrLn . render . ppHsDecl) hs
		       Left err -> putStrLn $ show err
	     else putStrLn "missing argument"
