{- |
Module     : $Header$
Description : Logic specific function implementation 4 Graded Modal Logic
Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : g.calin@jacobs-university.de
Stability   : provisional
Portability : non-portable (various -fglasgow-exts extensions)

Provides the implementation of the logic specific functions of the
ModalLogic class in the particular case of Graded Modal Logic
-}
{-# OPTIONS -fglasgow-exts #-}
module GMP.GradedML where

import GMP.GMPAS
import GMP.ModalLogic
import GMP.Lexer
import GMP.IneqSolver
import Debug.Trace

-- | Rules for Graded Modal Logic corresponding to the axiomatized rules
data GMLrules = GMLR [Int] [Int]
  deriving Show

instance ModalLogic GML GMLrules where
    flagML _ = Ang

    parseIndex = do n <- natural
                    return $ GML (fromInteger n)

    matchR r = let (q, w) = eccContent r
                   wrapR (x,y) = GMLR (map negate x) y
                   res = map wrapR (ineqSolver q (2^w))
               in trace("For q="++show q++"and w="++show w++"matchR("++show r++") is"++show res) res
-- res

    guessClause (GMLR n p) =
      let zn = zip (map negate n) [1..]
          zp = zip p [1+length n..]
          f l x = let aux = psplit l ((sum.fst.unzip.fst) x)
                      tmp = assoc aux ((snd.unzip.fst) x,(snd.unzip.snd) x)
                  in -- tmp
                     trace ( "GradedML.psplit result: "++show aux++"\nGradedML.assoc result: "++show tmp) tmp
          res = let tmp = concat (map (f zp) (split zn))
                in tmp
                   --trace ("zn: "++show zn++", zp: "++show zp) tmp
      in --res
         trace ("guessClause("++show (GMLR n p)++"): "++show res) res

{- | Create propositional clauses by associating each element of the 1st list
arg. to each element of the 2nd list arg. -}
assoc :: [([Int], [Int])] -> ([Int], [Int]) -> [PropClause]
assoc l u = map ((\x y -> Pimplies ((snd x)++(snd y)) ((fst x)++(fst y))) u) l

-- | Return all ways of separating the elements of a list into two lists
split :: [a] -> [([a], [a])]
split l =
  case l of
    []  -> [([],[])]
    h:t -> let x = split t
           in [(h:(fst q),snd q)|q <- x] ++ [(fst q,h:(snd q))|q <- x]

{- | Splitting function for positive coefficients. In second arg. we have the
 - sum of the current to be counted elements (the ones in J) and it returns
 - all pairs of indexes of positive coefficients which are good -}
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

-- | The size of a is: ]log_2(|a| + 1)[, where ].[ stands for ceiling
size :: Int -> Int
size i = ceiling (logBase 2 (fromIntegral (abs i + 1)) :: Double)

{- | Extract the content of a contracted clause by returning the grades of the
 - modal applications together with the bound for the elements of the solution
 - in terms of the computed length of the inequality -}
eccContent :: ModClause GML -> (Coeffs, Int)
eccContent (Mimplies n p) =
  let getGrade x =
        case x of
          Mapp (Mop (GML i) Angle) _ -> i
          _                          -> error "GradedML.getGrade"
      l1 = map (\x -> x + 1) (map getGrade n)        -- coeff for negative r_i
      l2 = map getGrade p                            -- coeff for positive r_i
      w = 1 + (length l1) + (length l2) + sum (map size l1) + sum (map size l2)
  in (Coeffs l1 l2, w)
