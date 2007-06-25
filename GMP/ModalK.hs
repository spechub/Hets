{-# OPTIONS -fglasgow-exts #-}
module ModalK where

import GMPAS
import ModalLogic

data Krules = KR Int

instance ModalLogic ModalK Krules where   
    parseIndex = return (ModalK ())
    matchRO ro = if (rkn ro) then [KR ((length ro)-1)] else []
    getClause r = let rec m =
                        case m of
                            0 -> Cl []
                            _ -> let Cl aux = rec(m-1)
                                 in Cl $ Lit (-m) : aux
                  in case r of
                        [KR n] -> let Cl x = rec n
                                      c = reverse(Lit (n+1) :x)
                                  in (Cl c) : []
                        _      -> []                        
                        
-- the RKn rule of the K modal logic ------------------------------------------
rkn :: [TVandMA t] -> Bool
rkn l =
    case l of
     []                 -> False
     (TVandMA (_,t):[]) -> if t then True else False
     (TVandMA (_,t):tl) -> if t then False else (rkn tl)
