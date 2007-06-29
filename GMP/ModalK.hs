{-# OPTIONS -fglasgow-exts #-}
module ModalK where

import GMPAS
import ModalLogic

data Krules = KR Int
    deriving Show

instance ModalLogic ModalK Krules where   
    parseIndex = return (ModalK ())
    matchRO ro = if (rkn ro) then [KR ((length ro)-1)] 
                             else []
    guessClause r = 
        case r of
            KR 0    -> [Cl [PLit 1]]
            KR n    -> let l = map NLit [1..n]
                           x = reverse l
                           c = reverse(PLit (n+1) : x)
                       in [Cl c]
                        
-- the RKn rule of the K modal logic ------------------------------------------
rkn :: [TVandMA t] -> Bool
rkn l =
    case l of
     []                 -> False
     (TVandMA (_,t):[]) -> if t then True else False
     (TVandMA (_,t):tl) -> if t then False else (rkn tl)
