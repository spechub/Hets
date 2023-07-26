{- |
Module      :  $Id$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

append a haskell Prelude string for programatica analysis
  or add CASL_DL/PredDatatypes.dol to CASL_DL/PredefinedSign.inline.hs
-}

module Main where

import System.Environment

main :: IO ()
main = do
    l <- getArgs
    preludeString <- readFile $ case l of
      [] -> "Haskell/ProgramaticaPrelude.hs"
      h : _ -> h
    str <- getContents
    putStrLn $ str ++ "\n " ++ show preludeString
