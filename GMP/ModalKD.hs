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
    flagML _ = Sqr
    parseIndex = return (ModalKD ())
    matchRO ro = let c = pnrkn ro
                     Implies (n,_) = ro
                 in case c of
                     P -> [KDPR (length n)]
                     N -> [KDNR (length n)]
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
pnrkn :: RoClause ModalKD -> Rchoice
pnrkn l =
    let Implies (n,p) = l
    in case p of
        []              -> if (n == []) 
                            then O
                            else N
        [MATV (_,True)] -> P
        _               -> O
