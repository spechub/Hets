{- |
Module      :  $Header$
Description :  Utils extending Data.List and Data.Set
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Data.ListSet where

import qualified Data.List as L
import qualified Data.Set as S

completeCols :: (Ord b) => [[(a,b)]] -> S.Set b
completeCols matrix = intersections (map sndsOf matrix)
     where sndsOf row = S.fromList (map snd row)

intersections :: (Ord a) => [S.Set a] -> S.Set a
intersections [] = S.empty
intersections family = foldl1 S.intersection family

s1 = S.fromList [1,2,3]
s2 = S.fromList [2,3,4]
s3 = S.fromList [3,4,5]
s4 = S.fromList [4,5,6]

s = [s1,s2,s3,s4]

{-

*Data.ListSet> intersections [s1,s2]
fromList [2,3]

*Data.ListSet> intersections [s1,s2,s3]
fromList [3]

*Data.ListSet> intersections [s1,s2,s4]
fromList []
-}
