{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ListUtils where

splitBy :: Eq a => a -> [a] -> [[a]]
splitBy x [] = []
splitBy x xs = let (l,rest) = break (==x) xs
                 in l : case rest of
                          []        -> []
                          (_:rest') -> splitBy x rest' 
