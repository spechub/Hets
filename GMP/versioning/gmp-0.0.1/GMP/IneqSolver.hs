{- | Module     : $Header$
  Description : Inequality Solver for Graded Modal Logics
  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
  License     : GPLv2 or higher
  Maintainer  : g.calin@jacobs-university.de
  Stability   : provisional
  Portability : non-portable (various -fglasgow-exts extensions)

  Provides an implementation for solving the system
         0 >= 1 + sum x_i*n_i + sum y_i*p_i
   with unknowns x_i and y_i within given limits.
 -}
module GMP.IneqSolver where

-- | Coefficients: negative\/positive signed grades on the left\/right.
data Coeffs = Coeffs [Int] [Int]
    deriving (Eq, Ord, Show)

-- | Datatype for negative\/positive unknowns; the second Int is the flag.
data IntFlag = IF Int Int
    deriving (Eq, Ord)

{- | Sort increasingly a list of pairs.
The sorting is done over the first element of the pair
-}
sort :: Ord a => [(a,b)] -> [(a,b)]
sort list =
  let insert x l =
        case l of
          h:t -> if (fst x < fst h)
                 then x:l
                 else h:(insert x t)
          []  -> [x]
  in case list of
       h:t -> insert h (sort t)
       []  -> []

-- | Compute the minimal point-wise extremal sum of an IntFlag list.
minSum :: [IntFlag] -> Int -> Int -> Int
minSum l lim c =
    case l of
      (IF x 0):t -> (minSum t lim c)-lim*x
      (IF x 1):t -> (minSum t lim c)+x
      []         -> c
      _          -> error "IneqSolver.minSum"

-- | Compute the maximal point-wise extremal sum of an IntFlag list.
maxSum :: [IntFlag] -> Int -> Int -> Int
maxSum l lim c =
    case l of
      (IF x 0):t -> (maxSum t lim c)-x
      (IF x 1):t -> (maxSum t lim c)+lim*x
      []         -> c
      _          -> error "IneqSolver.maxSum"

{- | Returns the updated bound for the unknown corresponding to the negative
 - coeff. h where t holds the coefficients for the not yet set unknowns -}
negBound :: Int -> [IntFlag] -> Int -> Int -> Int
negBound h t lim c =
        let tmp = case h of
                    0 -> -1--error "div by 0 @ IneqSolver.negBound"
                    _ -> div (negate(minSum t lim c)) h
        in if (tmp<0) then min tmp (-1) else (-1)

{- | Returns the updated bound for the unknown corresponding to the positive
 - coeff. h where t holds the coefficients for the not yet set unknowns -}
posBound :: Int -> [IntFlag] -> Int -> Int -> Int
posBound h t lim c =
        let tmp = case h of
                    0 -> lim--error "div by 0 @ IneqSolver.posBound"
                    _ -> div (negate(minSum t lim c)) h
        in if (tmp>0) then min tmp lim else lim

mapAppend :: a -> [[a]] -> [[a]]
mapAppend x list = map (\e->x:e) list

-- | Generate all posible solutions of unknowns
getUnknowns :: [IntFlag] -> Int -> Int -> [[Int]]
getUnknowns list lim c =
  if (maxSum list lim c<=0)
  then
    [map (\x->case x of
                (IF _ 0) -> (-1)
                (IF _ 1) -> lim
                _        -> error "IneqSolver.getUnknowns.if"
         ) list]
  else
    case list of
      (IF h 0):t -> let aux = negBound h t lim c
                    in concat (map (\x->mapAppend x (getUnknowns t lim (c+x*h)))
                                   [(-lim)..aux])
      (IF h 1):t -> let aux = posBound h t lim c
                    in concat (map (\x->mapAppend x (getUnknowns t lim (c+x*h)))
                                   [1..aux])
      []         -> []
      _          -> error "IneqSolver.getUnknowns.else"

{- | Returns all solutions (x,y) with 1<=-x_i,y_j<=L for the inequality
 -              0 >= 1 + sum x_i*n_i + sum y_j*p_j
 - with coefficients n_j>0, p_j>0 known -}
ineqSolver :: Coeffs -> Int -> [([Int],[Int])]
ineqSolver (Coeffs n p) bound =
  let combinedList = (map (\x -> IF x 0) n) ++ (map (\x -> IF x 1) p) -- merge lists & add flags
      (sortedList,indexOrder) = (unzip.sort) (zip combinedList [(1::Int)..]) -- sort by coefficents
      unOrdered = getUnknowns sortedList bound 1 -- get solutions for the sorted list of coefficients
      reOrder list order = (snd.unzip.sort) (zip order list) -- revert list to its initial order
      splitList l = case l of  -- split a result list in a pair as used by the implementation
                      h:t -> if (h<0) then let tmp = splitList t
                                           in (h:(fst tmp),snd tmp)
                                      else ([],l)
                      []  -> ([],[])
  in map (\l -> splitList (reOrder l indexOrder)) unOrdered
     -- for each element in the result list reorder it and split it

