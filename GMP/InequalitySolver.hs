module GMP.InequalitySolver where

import qualified Data.Map as Map

-- negative coeff first, positive after
data Coeffs = Coeffs [Int] [Int]
    deriving (Eq, Ord)

{- @ list : the list of coefficients on which we construct the map
 - @ lim : the upper bound for each solution of the inequality
 - @ return : first and second items in the 3-ple will be the lower and upper 
 - bound and the third will be the value of the coefficient corresponding to 
 - the index -}
initializeBounds :: [Int] -> Int -> Map.Map Int (Int, Int, Int)
initializeBounds list lim = 
  Map.fromList (zip [(1::Int)..] 
                    (zip3 (map (\_->1) [(1::Int)..]) 
                          (map (\_->lim) [(1::Int)..])
                          list
                    )
               )

{- Helping Functions -}
getLower :: Map.Map Int (Int, Int, Int) -> [Int] -- extract lower limit
getLower m = map (\(_,(x,_,_))->x) (Map.toList m)

getUpper :: Map.Map Int (Int, Int, Int) -> [Int] -- extract upper limit
getUpper m = map (\(_,(_,x,_))->x) (Map.toList m)

getCoeff :: Map.Map Int (Int, Int, Int) -> [Int] -- extract coefficient
getCoeff m = map (\(_,(_,_,x))->x) (Map.toList m)

linComb :: (Num a) => [a] -> [a] -> a -- compute linear sum
linComb l1 l2 = sum (map (\(x,y)->x*y) (zip l1 l2))

myLookup :: Int -> Map.Map Int a -> a -- lookup at a specific index in a map
myLookup i m = case Map.lookup i m of
                 Just x -> x
                 _      -> error "InequalitySolver.myLookup"

{- @ nMap : map corresponding to the negative unknowns/coefficients
 - @ posSum : linear combination (sum) of positive coefficients and unknowns
 - @ return : updated map corresponding to the negative unknowns/coefficients -}
negBoundUpdate :: Map.Map Int (Int, Int, Int) -> Int -> Int -> Map.Map Int (Int, Int, Int)
negBoundUpdate nMap posSum index =
  case index of
    0 -> nMap
    _ -> let mySum = 1 + posSum + linComb (getUpper nMap) (getCoeff nMap)
             -- compute current sum. this needs not to be done here since the
             -- upper bound does not modify, hence mySum is always the same.
             new i m = 
               let aux = myLookup i m
                   -- get the item we want to update from the map
                   temp = mySum - ((\(_,x,_)->x) aux)*((\(_,_,x)->x) aux)
                   -- update the sum by taking out the part given by the
                   -- current item
                   candidate = ceiling(fromIntegral temp/
                                       fromIntegral ((\(_,_,x)->(-x)) aux)
                                       ::Double)
                   -- compute the new candidate for the lower bound
               in max candidate ((\(x,_,_)->x) aux) 
                  -- return the updated lower bound
             replace i m = Map.adjust (\(_,u,c)->((new i m),u,c)) i m
             -- adjust the map by the new lower bound for the current position
         in negBoundUpdate (replace index nMap) posSum (index - 1)
            -- recurse over the other positions in the map

{- the updating of the positive bounds follows the general idea as used for 
 - the negative ones -}
posBoundUpdate :: Map.Map Int (Int, Int, Int) -> Int -> Int -> Map.Map Int (Int, Int, Int)
posBoundUpdate pMap negSum index =
  case index of
    0 -> pMap
    _ -> let mySum = negSum - 1 - linComb (getLower pMap) (getCoeff pMap)
             new i m = 
               let aux = myLookup i m
                   temp = mySum + ((\(x,_,_)->x) aux)*((\(_,_,x)->x) aux)
                   candidate = ceiling(fromIntegral temp/
                                       fromIntegral ((\(_,_,x)->x) aux)
                                       ::Double)
               in min candidate ((\(_,x,_)->x) aux)
             replace i m = Map.adjust (\(l,_,c)->(l,(new i m),c)) i m
         in posBoundUpdate (replace index pMap) negSum (index - 1)

updateCoeffBounds :: [Int] -> [Int] -> Int -> (Map.Map Int (Int,Int,Int),Map.Map Int (Int,Int,Int))
updateCoeffBounds n p lim = 
  let p_sum = length p -- actually this is: sum over 1 from 1 to (length p)
      n_map = initializeBounds n lim
      updated_n_map = negBoundUpdate n_map p_sum (length n)
      n_sum = sum (getUpper updated_n_map)
      p_map = initializeBounds p lim
      updated_p_map = posBoundUpdate p_map n_sum (length p)
  in (updated_n_map, updated_p_map)
------------------------------------------------------------------------------
{- generate all lists of given length and with elements between 1 and a limit
 - @ param n : fixed length
 - @ param lim : upper limit of elements
 - @ return : a list of all lists described above -}
negCands :: Int -> Int -> [[Int]]
negCands n lim =
  case n of
    0 -> [[]]
    _ -> [i:l| i <- [1..lim], l <- negCands (n-1) lim]

{- generate all lists of given length with elems between 1 and a limit such
 - that the side condition of Graded ML rule is satisfied
 - @ param n : fixed length
 - @ param lim : upper limit of elements
 - @ param s : sum (negative) which is previously computed and gets
               increased
 - @ param p : positive coefficients
 - @ return : list of all lists described above -}
posCands :: Int -> Int -> Int -> [Int] -> [[Int]]
posCands n lim s p =
 case n of
  0 -> [[]]
  _ -> [i:l|
        i<-[1..(min lim (floor (fromIntegral (abs s)/fromIntegral (head p)::Double)))],
        l <- (posCands (n-1) lim (s + i*(head p)) (tail p))]

{- gives all solutions in (1,lim) of the inequality with coeff n and p
 - @ param (Coeff n p) : negative and positive coefficients
 - @ param lim : limit for solution searching
 - @ return : solutions of the inequality, each stored as a pair -}
ineqSolver :: Coeffs -> Int -> [([Int],[Int])]
ineqSolver (Coeffs n p) lim =
  let (nMap,pMap) = updateCoeffBounds n p lim
      nl = getLower nMap; pu = getUpper pMap
      aux = 1 + linComb nl (getCoeff nMap) + linComb pu (getCoeff pMap)
  in if (aux<=0) then error "we reached this point"--[(nl,pu)]
     else let x = negCands (length n) lim
          in [(a,b)| a <- x, b <- posCands (length p) lim (linComb a n) p]
------------------------------------------------------------------------------
