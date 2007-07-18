{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS
import ModalLogic
import Lexer

data GMLrules = GMLrules ()

data SGimplies = SGimplies [Integer] [Integer]
    deriving (Eq, Ord)
instance ModalLogic Integer GMLrules where
--    orderIns _ = True
    flagML _ = Ang
    parseIndex = natural
    matchR _ = [GMLrules ()]
    guessClause r = case r of
                    _ -> []
                    -- GMLR n
-- determine r_i from inequality ----------------------------------------------
{- extract the content of the contracted clause
 - @ param (Mimplies n p) : contracted clause of which the content must be
 - extracted
 - @ return : the grade of the equivalent modal applications in the input param
 - The left list is for positive/negative signed grades -}
eccContent :: ModClause GML -> (SGimplies, Int)
eccContent (Mimplies n p) =
  let getGrade x =
        case x of
          Mapp (Mop (GML i) Angle) _ -> i
          _                          -> error "GradedML.getGrade"
      size i = ceiling (logBase 2 (fromIntegral (abs i + 1)) :: Double)
      l1 = map getGrade n 
      l2 = map (\x -> - x - 1) (map getGrade p)
      w = 1 + (length l1) + (length l2) + sum (map size l1) + sum (map size l2)
  in (SGimplies l1 l2, w)

{- 
roContent :: [MATV GML] -> ([SgnGrade],Integer)
roContent l =
  let size i = ceiling (logBase 2 (fromIntegral (abs i + 1)) :: Double)
  in case l of
      []     -> ([],2,0)
      x : xs -> let SgnGrade aux = getSG x
                    (roC,i,j) = roContent xs
                in if (fst aux)   -- we will return the number of positive r_is
                     then ((SgnGrade aux):roC, size (snd aux) + i, 1 + j)
                     else ((SgnGrade aux):roC, size (snd aux) + i, j)
-- by getting (x,y,z) = roContent ro 
-- x will contain the (sgn(r_i), k_i) pairs
-- y will be |W|-length(x)
-- z will be the number of positive-signed r_is
-}
-------------------------------------------------------------------------------
{-
ineqSol :: [MATV GML] -> [MATV GML]
ineqSol l = 
    let (x,y,z) = roContent l
        aux = length x
    in if (2*z > aux)
        then -- negative
        else -- pozitive
-}
