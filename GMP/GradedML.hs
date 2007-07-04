{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS
import ModalLogic
import Lexer

data GMLrules = GMLrules ()

-- r_i signs and k_is
data RSandK = RSandK (Bool, Integer)

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
getRK :: TVandMA GML -> RSandK
getRK x =
  case x of
    TVandMA (Mapp (Mop (GML i) Angle) _, t) -> RSandK (t,i)
    _                                       -> error "GradedML.getRK"
roContent :: [TVandMA GML] -> ([RSandK],Integer)
roContent l =
    case l of
        [] -> ([],2)
        x : xs -> let RSandK aux = getRK x
                      (roC,i) = roContent xs
                  in if (fst aux) 
                       then ((RSandK aux) : roC, 1 + (snd aux) + i)
                       else ((RSandK aux) : roC, (snd aux) + i)
-- by getting (x,y) = roContent ro x will contain the (sgn(r_i), k_i) pairs and
-- y will be |W|-length(x)
-------------------------------------------------------------------------------
