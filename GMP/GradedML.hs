{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS
import ModalLogic
import Lexer

data GMLrules = GMLR Int Int
  deriving Show
-- negative coeff first, positive after
data Coeffs = Coeffs [Int] [Int]
    deriving (Eq, Ord)
instance ModalLogic GML GMLrules where
--    orderIns _ = True
    flagML _ = Ang
    parseIndex = do n <- natural
                    return $ GML (fromInteger n)
    matchR r =
      let (q, w) = eccContent r
          pairs = ineqSolver q (2^w)
          append l =
            case l of
              [] -> []
              _  -> let (x,y) = head l
                    in (GMLR (length x) (length y)):append (tail l)
      in append pairs
    guessClause r = 
      case r of
        GMLR m n -> [Pimplies [(n+1)..n+m] [1..n]]
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
  _ -> [i:l|
        i<-[1..(min lim (floor (fromIntegral (abs s)/fromIntegral (head p)::Double)))],
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
