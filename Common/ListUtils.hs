{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ListUtils where

import Data.List                ( partition )

splitBy :: Eq a => a -> [a] -> [[a]]
splitBy x [] = []
splitBy x xs = let (l,rest) = break (==x) xs
                 in l : case rest of
                          []        -> []
                          (_:rest') -> splitBy x rest' 

-- | Divide a Set (List) into equivalence classes w.r. to eq
equivalence_Classes         :: (a -> a -> Bool) -> [a] -> [[a]]
equivalence_Classes _ []     = []
equivalence_Classes eq (x:l) = xs':(equivalence_Classes eq ys)
    where
        (xs, ys) = partition (eq x) l
        xs'      = (x:xs)

-- | Transform a list [l1,l2, ... ln] to (in sloppy notation)
-- [[x1,x2, ... ,xn] | x1<-l1, x2<-l2, ... xn<-ln]
permute      :: [[a]] -> [[a]]
permute []    = [[]]
permute [x]   = map (\y -> [y]) x
permute (x:l) = concat (map (distribute (permute l)) x)
    where
        distribute perms y = map ((:) y) perms

-- | Like 'and (zipWith p as bs)',
-- but must return False if lengths don't match
-----------------------------------------------------------}
zipped_all                :: (a -> b -> Bool) -> [a] -> [b] -> Bool
zipped_all _ []     []     = True
zipped_all p (a:as) (b:bs) = (p a b) && (zipped_all p as bs)
zipped_all _  _      _     = False
