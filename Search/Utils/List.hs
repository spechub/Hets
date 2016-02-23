{- |
Module      :  $Header$
Description :  Utils extending Data.List
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Utils.List where

import Data.List

filterMap :: (t -> Bool) -> (t -> a) -> [t] -> [a]
filterMap test fun lst = filterMap' lst []
    where filterMap' [] acc = reverse acc
          filterMap' (h:t) acc = filterMap' t acc'
              where acc' = if test h then (fun h):acc else acc
{-
*Utils.List> filterMap even (*3) [1,2,3,4,5]
[6,12]
-}

updateListAndGetIndex ::  (Eq a) => a -> [a] -> ([a], Int)
updateListAndGetIndex x table =
    case (findIndex (== x) table) 
    of Nothing -> (table ++ [x], length table)
       Just i  -> (table, i)

filterIndecesAndElems :: (a -> Bool) -> [a] -> [(a,Int)]
filterIndecesAndElems p lst = getByIndices indices tmpLst -- das geht effizienter mit einem einzigen Listendruchlauf
    where tmpLst = zip lst [0..((length lst) - 1)]
	  indices = findIndices p lst

{-
*Utils.List> filterIndecesAndElems even [1,2,3,4]
[(2,1),(4,3)]

*Utils.List> filterIndecesAndElems even [1,2,3,4,2]
[(2,1),(4,3),(2,4)]
-}

lookUpFirstEntry :: (Eq s)  => s -> [s] -> Maybe Int
lookUpFirstEntry s ss =
    case filterIndecesAndElems (s==) ss
	 of ((_,n):_) -> Just n
	    _ -> Nothing
{-
> lookUpFirstEntry 3 [1,2,3,4,5,4,3,2,1]
Just 2
-}

getByIndices :: [Int] -> [a] -> [a]
getByIndices indices lst = map (lst!!) admissbleIndices
    where admissbleIndices = filter (\x -> (x>=0) && (x<(length lst))) indices

{-
*Utils.List> getByIndices [1,3] ["a","b","c","d"]
["b","d"]
*Utils.List> getByIndices [3,1] ["a","b","c","d"]
["d","b"]
*Utils.List> getByIndices [1,5] ["a","b","c","d"]
["b"]
*Utils.List> getByIndices [3,1,5,2] ["a","b","c","d"]
["d","b","c"]
*Utils.List> getByIndices [] ["a","b","c","d"]
[]
*Utils.List> getByIndices [-1] ["a","b","c","d"]
[]
-}

mapAssoc :: [(Int,Int)] -> [a] -> [(a,a)]
mapAssoc intPair lst = tmpMap (length lst) intPair lst
    where tmpMap _ [] _ = []
	  tmpMap len ((m,n):rest) lst = 
	      if 0 <= m && 0 <= n && m < len && n < len
	      then (lst!!m,lst!!n):(tmpMap len rest lst)
	      else (tmpMap len rest lst)

{-
*Utils.List> mapAssoc [(1,3),(2,1)] ["a","b","c","d"]
[("b","d"),("c","b")]
*Utils.List> mapAssoc [(1,-3),(2,1)] ["a","b","c","d"]
[("c","b")]
*Utils.List> mapAssoc [(1,999),(2,1)] ["a","b","c","d"]
[("c","b")]
-}

listsToSortedIndices :: (Eq a)  => [a] -> [a] -> [Int]
listsToSortedIndices as bs = findIndices (\x -> elem x as) bs -- geht natuerlich effizienter


{- indices werden in aufsteigender Reihenfolge ausgeben
*Utils.List> listToSortedIndices [2,4] [1,2,3,4,5]
[1,3]
*Utils.List> listToSortedIndices [2,4] [4,2,3,4,5]
[0,1,3]
*Utils.List> listToSortedIndices [0,2,4] [1,2]
[1]
-}

listsToFirstIndices :: (Eq a)  => [a] -> [a] -> [Int]
listsToFirstIndices = (accIndices [] 0)
    where accIndices acc k [] _ = acc
	  accIndices acc k (a:as) bs =
	      case (elemIndex a bs)
	      of Just k -> accIndices (k:acc) k as bs
		 Nothing -> accIndices acc (k+1) as bs
    
makeRightUnique :: (Eq a) => [(a,a)] -> [(a,a)]
makeRightUnique lst = nubBy fstEq lst
    where fstEq (a,_) (b,_) = a == b

{-
*Utils.List> makeRightUnique [(1,3),(2,4),(1,2)]
[(1,3),(2,4)]
-}

isRightUnique :: (Eq a)  => [(a,a)] -> Bool
isRightUnique lst = (length lst') == (length $ makeRightUnique lst')
    where lst' = nub lst

{-
*Utils.List> isRightUnique [(1,3),(2,4),(1,2)]
False
*Utils.List> isRightUnique [(1,3),(2,4),(1,3)]
True
-}

filterNeq lst = filter unequalPair lst
    where unequalPair (x,y) = x /= y

--removeIdentities :: (Eq a)  => [(a,a)] -> [(a,a)]
--removeIdentities = filter (\(x,y) -> not (x == y))

mapShow :: (Show a) => String -> [a] -> [Char]
mapShow _ [] = ""
mapShow _ [x] = show x
mapShow sep (h:r) = show h ++ sep ++ (mapShow sep r)
-- mapShow kann man bestimmt eleganter schreiben. s. Show class


pprintList [] = putStrLn ""
pprintList (h:t) = putStrLn (show h) >> pprintList t
