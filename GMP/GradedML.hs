{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS()
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
-- ccContent ::
ccContent (Mimplies n p) =
  let getGrade x =
        case x of
          Mapp (Mop (GML i) Angle) _ -> i
          _                          -> error "GradedML.getGrade"
      size i = ceiling (logBase 2 (fromIntegral (abs i + 1)) :: Double)
  in SGimplies (map getGrade n) (map getGrade p) -- this needs to be improved 
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
