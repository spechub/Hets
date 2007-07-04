{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS
import ModalLogic
import Lexer

data GMLrules = GMLrules ()

-- r_i signs and k_is
data SgnGrade = SgnGrade (Bool, Integer)

instance ModalLogic Integer GMLrules where
    flagML _ = Ang
    parseIndex = natural
    matchRO ro = if (length ro == 0)
                  then []
                  else [GMLrules ()]
    guessClause r = case r of
                    _ -> []
                    -- GMLR n
-- determine r_i from inequality ----------------------------------------------
getSG :: TVandMA GML -> SgnGrade
getSG x =
  case x of
    TVandMA (Mapp (Mop (GML i) Angle) _, t) -> SgnGrade (t,i)
    _                                       -> error "GradedML.getRK"
roContent :: [TVandMA GML] -> ([SgnGrade],Integer)
roContent l =
  let size i = ceiling (logBase 2 (fromIntegral (abs i + 1)) :: Double)
  in case l of
      []     -> ([],2)
      x : xs -> let SgnGrade aux = getSG x
                    (roC,i) = roContent xs
                in if not (fst aux) 
                    then ((SgnGrade aux):roC, size (1 + (snd aux)) + i)
                    else ((SgnGrade aux):roC, size ((snd aux)) + i)
-- by getting (x,y) = roContent ro x will contain the (sgn(r_i), k_i) pairs and
-- y will be |W|-length(x)
-------------------------------------------------------------------------------
