{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
test the haskell parser

-}

module Main where

import Haskell.Hatchet.HsParseMonad
import Haskell.Hatchet.HsParser
import Haskell.Hatchet.HsSyn
import Haskell.Hatchet.HsPretty

main :: IO ()
main = do
	    s <- getContents
	    let r = parse s (SrcLoc 1 0) 0 []
	    putStrLn $ case r of
			 Ok _ hsM -> render $ ppHsModule hsM
			 Failed msg -> msg

