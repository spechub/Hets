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
{- recursion over the unkowns preceeded by positive coefficients
 - @ param p : positive coefficients
 - @ param y : current instantiation of the unknowns
 - @ param s : current sum (initially of unknowns corresponding to neg coeff)
 - @ param lim : the upper limit for the unknowns
 - @ return : solutions of the "partial" inequality i.e. solutions for the 
 -            unknowns preceeded by pos coeff for a certain instantiation of 
 -            the unknowns preceeded by neg coeff-}
posCoeff :: [Int] -> [Int] -> Int -> Int -> [[Int]]
posCoeff p y s lim =
  let news = s + sum [a*b| a <- p, b <- y]
      step l c w q =
        case l of
          [] -> []
          h:t -> let (u,v) = (head c, tail c)
                 in if (size h == w)||(q + u > -1)
                    then 1:(step t v w (q - (h-1)*u))
                    else (h + 1):t
  in if (news > -1)
     then []
     else let newy = step y p lim news
          in y:(posCoeff p newy s lim)
{- recursion on the unknowns preceeded by negative coefficients
 - @ param n : negative coefficients
 - @ param p : positive coefficients
 - @ param x : current instantiation of the unknowns
 - @ lim : the limit up to which to look for unknowns (2^18W^4)
 - @ return : solutions of the inequality from the "x" solution/instantiation 
 -            on -}
negCoeff :: [Int] -> [Int] -> [Int] -> Int -> [([Int],[Int])]
negCoeff n p x lim =
  let s = sum [a*b| a <- n, b <- x]
      y = map (\_ -> 1) p
      step l w = 
        case l of
          []  -> []
          h:t -> if (h == w)
                 then 1:(step t w)
                 else (h + 1):t
      newx = step x lim
  in if (newx == map (\_ -> 1) n)
     then []
     else (map (\w -> (x,w)) (posCoeff p y s lim)) ++ (negCoeff n p newx lim)
-- alternative ...
{- generate all lists of given length and with elements between 1 and a limit
 - @ param n : fixed length
 - @ param lim : upper limit of elements
 - @ return : a list of all lists described above -}
negCands :: Int -> Int -> [[Int]]
negCands n lim =
  let first = map (\_ -> 1) [1..n]
      next l x = 
        case l of
          []  -> []
          h:t -> if (h == x) 
                 then 1 : (next t x)
                 else (h + 1) : t
      aux l l0 x = 
        let nextl = next l x
        in if (nextl == l0) 
           then [l]
           else l : (aux nextl l0 x)
  in aux first first lim
{- gives all solutions in (1,lim) of the inequality with coeff n and p
 - @ param (Coeff n p) : negative and positive coefficients
 - @ param lim : limit for solution searching
 - @ return : solutions of the inequality, each stored as a pair -}
ineqSolver :: Coeffs -> Int -> [([Int],[Int])]
ineqSolver (Coeffs n p) lim = let x = map (\_ -> 1) n
                              in negCoeff n p x lim
-------------------------------------------------------------------------------
