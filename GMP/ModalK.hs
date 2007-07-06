{-# OPTIONS -fglasgow-exts #-}
module ModalK where

import GMPAS
import ModalLogic

data Krules = KR Int
    deriving Show

instance ModalLogic ModalK Krules where
    flagML _ = Sqr
    parseIndex = return (ModalK ())
    matchRO ro = if (rkn ro) 
                 then let Implies (n,_) = ro
                      in [KR (length n)] 
                 else []
    guessClause r = 
        case r of
            KR 0    -> [Cl [PLit 1]]
            KR n    -> let l = map NLit [1..n]
                           x = reverse l
                           c = reverse(PLit (n+1) : x)
                       in [Cl c]
                        
-- the RKn rule of the K modal logic ------------------------------------------
rkn :: RoClause ModalK -> Bool
rkn l =
    let Implies (_,p) = l
    in case p of
        [MATV (_,True)] -> True
        _               -> False
