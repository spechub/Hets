{-| 
   
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ListUtils where

import Data.List                ( groupBy )

-- | split list at separator elements, avoid empty sublists
splitBy :: Eq a => a -> [a] -> [[a]]
splitBy x xs = let (l, r) = break (==x) xs in 
    (if null l then [] else [l]) ++ (if null r then [] else splitBy x $ tail r)
-- suffix "By" usually indicates a (a -> a -> Bool) argument instead of Eq

-- | Divide a Set (List) into equivalence classes w.r. to eq
equivalence_Classes         :: (a -> a -> Bool) -> [a] -> [[a]]
equivalence_Classes = groupBy

-- | Transform a list [l1,l2, ... ln] to (in sloppy notation)
-- [[x1,x2, ... ,xn] | x1<-l1, x2<-l2, ... xn<-ln]
permute      :: [[a]] -> [[a]]
permute []    = [[]]
permute (x:l) = concatMap ((`map` permute l) . (:)) x
-- a better name would be "combine"

-- | Like 'and (zipWith p as bs)',
-- but must return False if lengths don't match
-----------------------------------------------------------}
zipped_all                :: (a -> b -> Bool) -> [a] -> [b] -> Bool
zipped_all _ []     []     = True
zipped_all p (a:as) (b:bs) = p a b && zipped_all p as bs
zipped_all _  _      _     = False
