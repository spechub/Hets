{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS
import ModalLogic
import Lexer

data GMLrules = GMLrules ()
-- negative coeff first, positive after
data Coeffs = Coeffs [Int] [Int]
    deriving (Eq, Ord)
instance ModalLogic Integer GMLrules where
--    orderIns _ = True
    flagML _ = Ang
    parseIndex = natural
    matchR _ = [GMLrules ()]
    guessClause r = case r of
                    _ -> []
-------------------------------------------------------------------------------
{- compute the size of a number as specified in the paper
 - @ param i : the given integer
 - @ return : the size of i -}
size :: Int -> Int
size i = ceiling (logBase 2 (fromIntegral (abs i + 1)) :: Double)
{- extract the content of the contracted clause
 - @ param (Mimplies n p) : contracted clause
 - @ return : the grade of the equivalent modal applications in the input param
 -            and the length of the inequality
 - left: negative signed grades; right: positive signed grades -}
eccContent :: ModClause GML -> (Coeffs, Int)
eccContent (Mimplies n p) =
  let getGrade x =
        case x of
          Mapp (Mop (GML i) Angle) _ -> i
          _                          -> error "GradedML.getGrade"
      l1 = map (\x -> - x - 1) (map getGrade n)      -- coeff for negative r_i
      l2 = map getGrade p                            -- coeff for positive r_i
      w = 1 + (length l1) + (length l2) + sum (map size l1) + sum (map size l2)
  in (Coeffs l1 l2, w)
-------------------------------------------------------------------------------
{- linear combination of elements in the two lists
 - @ param l1 : integer list [x1,..,xk]
 - @ param l2 : integer list [y1,..,yh]
 - @ return : the sum : \sum_{i=1}^{min(k,h)} xi * yi -}
--linComb :: [Int] -> [Int] -> Int
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
 - @ param s : sum (negative) which is previously computed and gets increased
 - @ param p : positive coefficients
 - @ return : list of all lists described above -}
posCands :: Int -> Int -> Int -> [Int] -> [[Int]]
posCands n lim s p =
 case n of
  0 -> [[]]
--_ -> [i:l| i <- [1..lim], l <- posCands (n-1) lim s p, s + doSum p (i:l) < 0]
  _ -> [i:l|
        i<-[1..(min lim (floor (fromIntegral (abs s)/fromIntegral (head p))))],
        l <- (posCands (n-1) lim (s + i*(head p)) (tail p))]
{- gives all solutions in (1,lim) of the inequality with coeff n and p
 - @ param (Coeff n p) : negative and positive coefficients
 - @ param lim : limit for solution searching
 - @ return : solutions of the inequality, each stored as a pair -}
ineqSolver :: Coeffs -> Int -> [([Int],[Int])]
ineqSolver (Coeffs n p) lim = 
  let x = negCands (length n) lim
      linComb l1 l2 =
        if (l1 == [])||(l2==[])
        then 0
        else (head l1)*(head l2) + linComb (tail l1) (tail l2)
  in [(a,b)| a <- x, b <- posCands (length p) lim (linComb a n) p]
-------------------------------------------------------------------------------
