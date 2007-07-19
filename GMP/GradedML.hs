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
posCoeff p y s lim =
  [[]]
{-
  let news = s + sum [a*b| a <- p, b <- y]
      
  in if (news > -1)
     then []
     else let newy = step y lim
              step y lim =
          in 
-}
{- recursion on the unknowns preceeded by negative coefficients
 - @ param n : negative coefficients
 - @ param p : positive coefficients
 - @ param x : current instantiation of the unknowns
 - @ lim : the limit up to which to look for unknowns
 - @ return : solutions of the inequality with instantiations of unknowns
 - preceeded by negative coeff following the "x" instantiation -}
negCoeff :: [Int] -> [Int] -> [Int] -> Int -> [([Int],[Int])]
negCoeff n p x lim =
  let s = sum [a*b| a <- n, b <- x]
      y = map (\_ -> 1) p
      step l w = 
        case l of
          []  -> []
          h:t -> if (size h == w)
                 then 1:(step t w)
                 else (h + 1):t
      newx = step x lim
  in if (newx == map (\w -> 1) n)
     then []
     else (map (\w -> (x,w)) (posCoeff p y s lim)) ++ (negCoeff n p newx lim)
{- gives all solutions in (1,lim) of the inequality with coeff n and p
 - @ param (Coeff n p) : negative and positive coefficients
 - @ param lim : limit for solution searching
 - @ return : solutions of the inequality, each stored as a pair -}
ineqSolver :: Coeffs -> Int -> [([Int],[Int])]
ineqSolver (Coeffs n p) lim = let x = map (\_ -> 1) n
                              in negCoeff n p x lim
-------------------------------------------------------------------------------
