{-# OPTIONS -fglasgow-exts #-}
module GMP.GradedML where

import GMP.GMPAS
import GMP.ModalLogic
import GMP.Lexer
import GMP.InequalitySolver

data GMLrules = GMLR [Int] [Int]
  deriving Show

instance ModalLogic GML GMLrules where
    flagML _ = Ang

    parseIndex = do n <- natural
                    return $ GML (fromInteger n)

    matchR r = let (q, w) = eccContent r
                   wrapR (x,y) = GMLR (map negate x) y
               in map wrapR (ineqSolver q (2^w-1))

    guessClause (GMLR n p) =
      let zn = zip n [1..]
          zp = zip p [1+length n..]
          f l x = let aux = psplit l ((sum.fst.unzip.fst) x)
                  in assoc aux ((snd.unzip.fst) x,(snd.unzip.snd) x)
      in concat (map (f zp) (split zn))

-------------------------------------------------------------------------------
{- associate the elements of l with x
 - @ param l : list of pairs of lists of integers
 - @ param u : pair of lists of integers
 - @ return : list of propositional clauses (associated and wrapped lists) -}
assoc :: [([Int], [Int])] -> ([Int], [Int]) -> [PropClause]
assoc l u = map ((\x y -> Pimplies ((snd x)++(snd y)) ((fst x)++(fst y))) u) l

{- spliting function
 - @ param l : list to be split
 - @ return : all pairs of lists which result by spliting l -}
split :: [a] -> [([a], [a])]
split l =
  case l of
    []  -> [([],[])]
    h:t -> let x = split t
           in [(h:(fst q),snd q)|q <- x] ++ [(fst q,h:(snd q))|q <- x]

{- splitting function for positive coefficients
 - @ param l : list to be split
 - @ param s : sum of the current to be counted elements (the ones in J)
 - @ return : all pairs of indexes of positive coefficients which are good -}
psplit :: (Num a, Ord a) => [(a, b)] -> a -> [([b], [b])]
psplit l s =
    if (s < 0)
    then case l of
           []  -> [([],[])]
           h:t -> if (s + (fst h) < 0)
                  then let aux1 = psplit t (s + (fst h))
                           aux2 = psplit t s
                       in [((snd h):(fst q),snd q)|q <- aux1] ++
                          [(fst q,(snd h):(snd q))|q <- aux2]
                  else let aux = psplit t s
                       in [(fst q,(snd h):(snd q))|q <- aux]
    else []

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
      l1 = map (\x -> x + 1) (map getGrade n)        -- coeff for negative r_i
      l2 = map getGrade p                            -- coeff for positive r_i
      w = 1 + (length l1) + (length l2) + sum (map size l1) + sum (map size l2)
  in (Coeffs l1 l2, 18*w^(4::Int))
-------------------------------------------------------------------------------
