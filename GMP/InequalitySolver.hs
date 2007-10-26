module GMP.InequalitySolver where

import qualified Data.Map as Map

-- negative coeff first, positive after
data Coeffs = Coeffs [Int] [Int]
    deriving (Eq, Ord)

{- @ list : the list of coefficients starting from which we construct the map
 - @ lim : the upper bound for each unknown solution of the inequality
 - @ return : first and second items in the 3-uple will be the lower and upper
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
 - @ posSum : linear combination (sum) of positive coefficients and lower
 -            bounds of unknowns
 - @ index : index of the item in the map set to be updated
 - @ return : updated map corresponding to the negative coefficients -}
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

{- @ pMap : map corresponding to the positive unknowns/coefficients
 - @ negSum : linear combination (sum of products) of negative coefficients 
 -            and upper bounds of unknowns 
 - @ index : index of the item in the map set to be updated
 - @ return : updated map corresponding to the positive coefficients -}
posBoundUpdate :: Map.Map Int (Int, Int, Int) -> Int -> Int -> Map.Map Int (Int, Int, Int)
posBoundUpdate pMap negSum index =
  case index of
    0 -> pMap
    _ -> let mySum = negSum - 1 - linComb (getLower pMap) (getCoeff pMap)
             new i m = 
               let aux = myLookup i m
                   temp = mySum + ((\(x,_,_)->x) aux)*((\(_,_,x)->x) aux)
                   -- note that the candidate might turn up to be negative ...
                   candidate = ceiling(fromIntegral temp/
                                       fromIntegral ((\(_,_,x)->x) aux)
                                       ::Double)
               in min (max candidate 0) ((\(_,x,_)->x) aux)
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
{- generate all lists of known length n, with each element between the limits
 - given in the indexed map nMap
 - @ param n : fixed length
 - @ param nMap : map where the bounds for each element of the list are stored
 - @ return : a list of all lists as described above -}
negCands :: Int -> Map.Map Int (Int, Int, Int) -> [[Int]]
negCands n nMap =
  case n of
    0 -> [[]]
    _ -> let aux = myLookup n nMap
             l = (\(x,_,_)->x) aux
             u = (\(_,x,_)->x) aux
         in [h:t| h <- [l..u], t <- negCands (n-1) nMap]

{- generate all lists of given length with elem's between the lower and upper
 - limit given from nMap such that the side condition of the Graded ML rule is satisfied
 - @ param n : fixed length
 - @ param pMap : map where the bounds and corresponding coefficient for each
 -                unknown are stored
 - @ param s : sum (negative) which is previously computed and gets
               increased
 - @ return : list of all lists described as above -}
posCands :: Int -> Map.Map Int (Int, Int, Int) -> Int -> [[Int]]
posCands n pMap s=
 case n of
  0 -> [[]]
  _ -> let aux = myLookup n pMap
           l = (\(x,_,_)->x) aux
           u = (\(_,x,_)->x) aux
           c = (\(_,_,x)->x) aux
           -- foo says how many y's at most fit in |x|
           foo x y = floor (fromIntegral (abs x)/fromIntegral y::Double)
       in [h:t| h <- [l..(min u (foo s c))], t <- posCands (n-1) pMap (s+h*c)]

{- gives all solutions in (1,lim) of the inequality with coeff n and p
 - @ param (Coeff n p) : negative and positive coefficients
 - @ param lim : upper bound for unknowns
 - @ return : solutions of the inequality, each stored as a pair -}
ineqSolver :: Coeffs -> Int -> [([Int],[Int])]
ineqSolver (Coeffs n p) lim = -- error (show n ++ " " ++ show p)
  let (nMap,pMap) = updateCoeffBounds n p lim
      nl = getLower nMap; pu = getUpper pMap
      aux = 1 + linComb nl (getCoeff nMap) + linComb pu (getCoeff pMap)
  in if (aux<=0) then -- error ("nMap: " ++ show nMap ++ " pMap: " ++ show pMap) 
                      [(nl,pu)]
     else let x = negCands (length n) nMap
          in [(a,b)| a <- x, b <- posCands (length p) pMap (linComb a n)]
------------------------------------------------------------------------------
