{- | Module     : $Header$
 -  Description : Inequality Solver for Graded Modal Logics
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : non-portable (various -fglasgow-exts extensions)
 -
 -  Provides an implementation for solving the system 
 -         0 >= 1 + sum x_i*n_i + sum y_i*p_i
 -  with unknowns x_i and y_i within given limits -}
module GMP.InequalitySolver where

-- | Coefficients datatype : negative on left and positive on right side
data Coeffs = Coeffs [Int] [Int]
    deriving (Eq, Ord)

{- | Sort increasingly a list of pairs. If the flag is true than the sorting is
 - done by the first element in the pair, otherwise by the second -}
sort :: [(Int,Int)] -> [(Int,Int)]
sort list =
  let insert x l =
        case l of
          h:t -> if (fst x < fst h) then x:l
                                    else h:(insert x t)
          []  -> [x]
  in case list of
       h:t -> insert h (sort t)
       []  -> []

{- | Returns the updated bound for the unknown corresponding to the negative
 - coeff. h where n & p hold the coefficients for the not yet set unknowns -}
negBound :: Int -> [Int] -> [Int] -> Int -> Int -> Int
negBound h n p c lim =
        let tmp = fromIntegral (c+lim*(sum p)+sum n)/fromIntegral h :: Double
        in if (tmp>0) then max (ceiling tmp) 1 else 1
{- | Returns the updated bound for the unknown corresponding to the positive
 - coeff. h where p holds the coefficients for the not yet set unknowns -}
posBound :: Int -> [Int] -> Int -> Int -> Int
posBound h p c lim =
        let tmp = fromIntegral (-c-sum p)/fromIntegral h :: Double
        in if (tmp>0) then min (floor tmp) lim else lim

-- | Append an element to each fst. element of each element of a list of pairs
mapAppendFst :: a -> [([a],[a])] -> [([a],[a])]
mapAppendFst x list = map (\e->(x:(fst e), snd e)) list

-- | Append an element to each snd. element of each element of a list of pairs
mapAppendSnd :: a -> [([a],[a])] -> [([a],[a])]
mapAppendSnd x list = map (\e->(fst e, x:(snd e))) list

-- | Generate all possible solutions of unknowns corresp. to positive coeffs.
getPosUnknowns :: [Int] -> Int -> Int -> [([Int], [Int])]
getPosUnknowns p lim c =
  if (c+lim*(sum p)<=0)
  then [([], map (\_->lim) p)]
  else
    case p of
      h:t -> let aux = posBound h t c lim
             in concat (map (\x->mapAppendSnd x (getPosUnknowns t lim (c+x*h)))
                            [1..aux])
      []  -> [([],[])]

-- | Generate all posible solutions of unknowns
getUnknowns :: [Int] -> [Int] -> Int -> Int -> [([Int], [Int])]
getUnknowns n p lim c =
  if (c+sum n+lim*(sum p)<=0)
  then [(map (\_->1) n, map (\_->lim) p)]
  else
    case n of
      h:t -> let aux = negBound (abs h) t p c lim
             in concat (map (\x->mapAppendFst x (getUnknowns t p lim (c+x*h)))
                            [aux..lim])
      []  -> getPosUnknowns p lim c

{- | Returns all solutions (x,y) with 1<=x_i,y_j<=L for the inequality
 -              0 >= 1 + sum x_i*n_i + sum y_j*p_j
 - with coefficients n_j<0, p_j>0 known -}
ineqSolver :: Coeffs -> Int -> [([Int],[Int])]
ineqSolver (Coeffs n p) bound = 
  let (newN,nIndexOrder) = let tmp = (unzip.sort) (zip (map negate n) [1..])
                           in (map negate (fst tmp),snd tmp)
      (newP,pIndexOrder) = (unzip.sort) (zip p [1..])
      aux = getUnknowns newN newP bound 1
      funComp list indexOrder = (snd.unzip.sort) (zip indexOrder list)
  in map (\(x,y)->(funComp x nIndexOrder, funComp y pIndexOrder)) aux
{-  
  in error ("n: " ++ show n ++ " p: " ++ show p ++ " lim: " ++ show bound
                                                ++ " res: " ++ show aux)
-}
