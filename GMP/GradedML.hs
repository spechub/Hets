{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS()
import ModalLogic
import Lexer

data GMLrules = GMLrules ()

-- r_i signs and k_is
data SgnGrade = SgnGrade (Bool, Integer)
--    deriving (Eq, Ord)
instance ModalLogic Integer GMLrules where
    flagML _ = Ang
    parseIndex = natural
    matchR _ = [GMLrules ()]
    guessClause r = case r of
                    _ -> []
                    -- GMLR n
-- determine r_i from inequality ----------------------------------------------
{-
getSG :: MATV GML -> SgnGrade
getSG x =
  case x of
    MATV (Mapp (Mop (GML i) Angle) _, t) -> if t 
                                              then SgnGrade (t,-1-i)
                                              else SgnGrade (t,i)
    _                                    -> error "GradedML.getRK"
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
