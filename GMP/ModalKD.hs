{-# OPTIONS -fglasgow-exts #-}
module ModalKD where

import GMPAS
import ModalLogic

data KDrules = KDPR Int
             | KDNR Int
data Rchoice = P | N | O
    deriving Eq
instance ModalLogic ModalKD KDrules where
    parseIndex = return (ModalKD ())
    matchRO ro = let c = pnrkn ro 
                 in if (c == P)
                    then [KDPR ((length ro)-1)]
                    else if (c == N)
                    then [KDNR (length ro)]
                    else []
    getClause r = 
        case r of
            KDPR n -> let x = map NLit [1..n]
                          c = reverse(PLit (n+1) : x)
                      in [Cl c]
            KDNR n -> let c = reverse(map NLit [1..n])
                      in [Cl c]
-- verifier for the KD positive & negative rule of the KD modal logic ---------
pnrkn :: [TVandMA t] -> Rchoice
pnrkn l =
    case l of
     []                 -> O
     (TVandMA (_,t):[]) -> if t then P else N
     (TVandMA (_,t):tl) -> if t then O else (pnrkn tl)
