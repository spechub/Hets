{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS
import ModalLogic
import Lexer

data GMLrules = GMLrules ()

data Coeffs = Coeffs [Integer] [Integer]
    deriving (Eq, Ord)
instance ModalLogic Integer GMLrules where
--    orderIns _ = True
    flagML _ = Ang
    parseIndex = natural
    matchR _ = [GMLrules ()]
    guessClause r = case r of
                    _ -> []
-------------------------------------------------------------------------------
{- extract the content of the contracted clause
 - @ param (Mimplies n p) : contracted clause
 - @ return : the grade of the equivalent modal applications in the input param
 -            and the length of the inequality
 - left: negative signed grades; right: positive signed grades -}
eccContent :: ModClause GML -> (SGimplies, Int)
eccContent (Mimplies n p) =
  let getGrade x =
        case x of
          Mapp (Mop (GML i) Angle) _ -> i
          _                          -> error "GradedML.getGrade"
      size i = ceiling (logBase 2 (fromIntegral (abs i + 1)) :: Double)
      l1 = map (\x -> - x - 1) (map getGrade n)
      l2 = map getGrade p
      w = 1 + (length l1) + (length l2) + sum (map size l1) + sum (map size l2)
  in (Coeffs l1 l2, w)
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
