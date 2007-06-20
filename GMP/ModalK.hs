module ModalK where

import GMPAS
import ModalLogic
import GMPSAT

instance ModalLogic ModalK where   
    parseIndex = return (ModalK ())
    matchRO ro = if (rkn ro) then [(length ro)-1] else []
-- the RKn rule ok the K modal logic -------------------------------------------
rkn l =
    case l of
     []                 -> False
     (TVandMA (x,t):[]) -> if t then True else False
     (TVandMA (x,t):tl) -> if t then False else (rkn tl)
