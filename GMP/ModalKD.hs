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
    getClause r = let prec m = case m of
                                0 -> Cl []
                                _ -> let Cl aux = prec(m-1)
                                     in (Cl ((Lit (-m)):aux)
                      nrec w = case w of
                                0 -> Cl []
                                _ -> let Cl aux = nrec(w-1)
                                     in (Cl (Lit w):aux)
                  in case r of
                        [KDPR n] -> let Cl x = prec n
                                        c = reverse((Lit (n+1)):x)
                                    in ((Cl c):[])
                        [KDNR n] -> let Cl x = nrec n
                                    in (Cl reverse(x)):[]
                        _        -> []
-- verifier for the KD positive & negative rule of the KD modal logic ---------
pnrkn :: [TVandMA t] -> Rchoice
pnrkn l =
    case l of
     []                 -> O
     (TVandMA (_,t):[]) -> if t then P else N
     (TVandMA (_,t):tl) -> if t then O else (pnrkn tl)
