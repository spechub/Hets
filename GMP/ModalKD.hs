{-# OPTIONS -fglasgow-exts #-}
module ModalKD where

import GMPAS
import ModalLogic

data KDrules = KDPR Int
             | KDNR Int
    deriving Show
data Rchoice = P | N | O
    deriving Eq

instance ModalLogic ModalKD KDrules where
    preprocess f =
        case f of
            T                     -> T
            F                     -> F
            Neg ff                -> Neg (preprocess ff)
            Junctor f1 j f2       -> Junctor (preprocess f1) j (preprocess f2)
            Mapp (Mop i Angle) ff -> Neg $ Mapp (Mop i Square) (Neg ff)
            _                     -> f
    parseIndex = return (ModalKD ())
    matchRO ro = let c = pnrkn ro 
                 in case c of
                     P -> [KDPR ((length ro)-1)]
                     N -> [KDNR (length ro)]
                     _ -> []
    guessClause r = 
        case r of
            KDPR 0 -> [Cl [PLit 1]]
            KDPR n -> let l = map NLit [1..n]
                          x = reverse l
                          c = reverse(PLit (n+1) : x)
                      in [Cl c]
            KDNR n -> let c = map NLit [1..n]
                      in [Cl c]
-- verifier for the KD positive & negative rule of the KD modal logic ---------
pnrkn :: [TVandMA t] -> Rchoice
pnrkn l =
    case l of
     []                 -> O
     (TVandMA (_,t):[]) -> if t then P else N
     (TVandMA (_,t):tl) -> if t then O else (pnrkn tl)
