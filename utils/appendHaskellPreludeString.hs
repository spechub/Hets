{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
append a haskell Prelude string for programatica analysis

-}
module Main where

import System.Environment

main :: IO ()
main = do 
    l <- getArgs 
    let preludeFileName = if null l then "Haskell/ProgramaticaPrelude.hs"
                          else head l
    preludeString <- readFile preludeFileName
    str <- getContents
    putStrLn (str ++ "\n " ++ show preludeString)  
    
