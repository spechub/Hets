module GMP.InequalitySolver where

-- | Coefficients datatype : negative on left and positive on right side
data Coeffs = Coeffs [Int] [Int]
    deriving (Eq, Ord)

{- | Returns the updated bound for the unknown corresponding to the negative
 - coeff. h where n & p hold the coefficients for the not yet set unknowns -}
updateNegBound :: Int -> [Int] -> [Int] -> Int -> Int -> Int
updateNegBound h n p c lim = 
        let tmp = fromIntegral (c+lim*(sum p)+sum n)/fromIntegral h :: Double
        in if (tmp>0) then max (ceiling tmp) 1 else 1
{- | Returns the updated bound for the unknown corresponding to the positive
 - coeff. h where p holds the coefficients for the not yet set unknowns -}
updatePosBound :: Int -> [Int] -> Int -> Int -> Int
updatePosBound h p c lim =
        let tmp = fromIntegral (-c-sum p)/fromIntegral h :: Double
        in if (tmp>0) then min (floor tmp) lim else lim

-- | Append w to the first element of the pair result of func w
negAddAndCall :: (a -> [([a], [a])]) -> a -> [([a], [a])]
negAddAndCall func w = let aux = func w 
                       in zip (map ((w:).fst) aux) (map snd aux)
-- | Append w to the second element of the pair result of func w
posAddAndCall :: (a -> [([a], [a])]) -> a -> [([a], [a])]
posAddAndCall func w = let aux = func w
                       in zip (map fst aux) (map ((w:).snd) aux)

{- | Returns all solutions (x,y) with 1<=x_i,y_j<=lim of the inequality
 -              0 >= 1 + sum x_i*n_i + sum y_j*p_j
 - with coefficients n_j<0, p_j>0 known -}
ineqSolver :: Coeffs -> Int -> [([Int],[Int])]
ineqSolver (Coeffs x y) bound = recurseAll x y bound 1
------------------------------------------------------------------------------
recursePos :: [Int] -> Int -> Int -> [([Int], [Int])]
recursePos p lim c =
        if (c+lim*(sum p)<=0)
        then [([], map (\_->lim) p)]
        else case p of
               h:t -> let aux = updatePosBound h t c lim
                      in concat (map (posAddAndCall (recursePos t lim))
                                     (map ((c+).(h*)) [1..aux]))
               []  -> [([],[])]

recurseAll :: [Int] -> [Int] -> Int -> Int -> [([Int], [Int])]
recurseAll n p lim c =
        if (c+sum n+lim*(sum p)<=0) 
        then [(map (\_->1) n, map (\_->lim) p)]
        else case n of
               h:t -> let aux = updateNegBound (abs h) t p c lim
                      in concat (map (negAddAndCall (recurseAll t p lim))
                                     (map ((c+).(h*)) [aux..lim]))
               []  -> recursePos p lim c

