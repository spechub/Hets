module GMP.InequalitySolver where

import qualified Data.Map as Map

{- @ list : the list of coefficients on which we construct the map
 - @ lim : the upper bound for each solution of the inequality
 - @ return : first and second items in the 3-ple will be the lower and upper 
 - bound and the third will be the value of the coefficient corresponding to 
 - the index -}
setBounds :: [Int] -> Int -> Map.Map Int (Int, Int, Int)
setBounds list lim = 
  Map.fromList (zip [(1::Int)..] 
                    (zip3 (map (\_->1) [(1::Int)..]) 
                          (map (\_->lim) [(1::Int)..])
                          list
                    )
               )

{- @ nMap : map corresponding to the negative unknowns/coefficients
 - @ pMap : map corresponding to the positive unknowns/coefficients
 - @ return :
 -}
negBoundUpdate :: Map.Map Int (Int, Int, Int) -> Int -> Int -> Map.Map Int (Int, Int, Int)
negBoundUpdate nMap posSum index =
  case index of
    0 -> nMap
    _ -> let getUpper m = map (\(_,(_,x,_))->x) (Map.toList m)
             getCoeff m = map (\(_,(_,_,x))->x) (Map.toList m)
             linComb l1 l2 = sum (map (\(x,y)->x*y) (zip l1 l2))
             mySum = 1 + posSum + linComb (getUpper nMap) (getCoeff nMap)
             myLookup i m = case Map.lookup i m of
                              Just x -> x
                              _      -> error "negBoundUpdate.myLookup"
             new i m = 
               let aux = myLookup i m
                   temp = mySum - ((\(_,x,_)->x) aux)*((\(_,_,x)->x) aux)
                   candidate = ceiling(fromIntegral temp/
                                       fromIntegral ((\(_,_,x)->(-x)) aux)
                                       ::Double)
               in max candidate ((\(x,_,_)->x) aux)
             replace i m = Map.adjust (\(_,u,c)->((new i m),u,c)) i m
         in negBoundUpdate (replace index nMap) posSum (index - 1)

{-
 -}
posBoundUpdate :: Map.Map Int (Int, Int, Int) -> Int -> Int -> Map.Map Int (Int, Int, Int)
posBoundUpdate pMap negSum index =
  case index of
    0 -> pMap
    _ -> let getLower m = map (\(_,(x,_,_))->x) (Map.toList m)
             getCoeff m = map (\(_,(_,_,x))->x) (Map.toList m)
             linComb l1 l2 = sum (map (\(x,y)->x*y) (zip l1 l2))
             mySum = negSum - 1 - linComb (getLower pMap) (getCoeff pMap)
             myLookup i m = case Map.lookup i m of
                              Just x -> x
                              _      -> error "negBoundUpdate.myLookup"
             new i m = 
               let aux = myLookup i m
                   temp = mySum + ((\(x,_,_)->x) aux)*((\(_,_,x)->x) aux)
                   candidate = ceiling(fromIntegral temp/
                                       fromIntegral ((\(_,_,x)->x) aux)
                                       ::Double)
               in min candidate ((\(_,x,_)->x) aux)
             replace i m = Map.adjust (\(l,_,c)->(l,(new i m),c)) i m
         in posBoundUpdate (replace index pMap) negSum (index - 1)
{-
{- update the coefficicients' bounds
 - @ param negMap : indexed pairs of (lower bound, upper bound) items and 
 -                  quantifier for each "negative" coefficient 
 - @ param posMap : indexed pairs of (lower bound, upper bound) items and
 -                  quantifier for each "positive" coefficient
 - @ return : map containing the updated bounds for the negative 
 -            coefficients -} 
negCoeffBoundsUpdate negMap posMap =
  let setBound4_ith negMap posMap i=
        let aux = 1 + sum (map (\(_,((_,_),x))->x) (Map.toList posMap)) - 
                  sum (map (\(x,y)->x*y) 
                           (zip (map (\(_,((_,x),_))->x) (Map.toList negMap))
                                (map (\(_,((_,_),x))->x) (Map.toList negMap))
                           )
                      )
            update v negMap index =
              case Map.lookup index negMap of
                Just x -> Map.adjust 
                              (\((l,u),c)->((max l ceiling(fromIntegral (v-c*u)/fromIntegral -c::Double),u),coeff))
                              index negMap
                _      -> error "updateCoeffBounds.update"
        in 
  in case i of
       0 -> negMap
       _ -> negCoeffBoundsUpdate (setBound4_ith (update aux negMap)) (i-1)

{- generate all lists of given length and with elements between 1 and a limit
 - @ param n : fixed length
 - @ param lim : upper limit of elements
 - @ return : a list of all lists described above -}
negCands :: Int -> Int -> [Int] -> [[Int]]
negCands index lim n p =
  let aux = negCoeffBoundsUpdate (setCoeffBounds n lim) (setCoeffBounds p lim)
  in case index of
       0 -> [[]]
       _ -> [i:l| i <- [(getLowerBound aux index)..(getUpperBound aux index)],
                  l <- negCands (index-1) lim n]

{- generate all lists of given length with elems between 1 and a limit such
 - that the side condition of Graded ML rule is satisfied
 - @ param n : fixed length
 - @ param lim : upper limit of elements
 - @ param s : sum (negative) which is previously computed and gets increased
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
ineqSolver :: [Int] -> [Int]-> Int -> [([Int],[Int])]
ineqSolver n p lim =
  let x = negCands (length n) lim n
      linComb l1 l2 =
        if (l1 == [])||(l2==[])
        then 0
        else (head l1)*(head l2) + linComb (tail l1) (tail l2)
  in [(a,b)| a <- x, b <- posCands (length p) lim (linComb a n) p]
-}
