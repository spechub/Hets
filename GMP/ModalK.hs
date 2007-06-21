module ModalK where

import GMPAS
import ModalLogic
import GMPSAT

instance ModalLogic ModalK Krules where   
    parseIndex = return (ModalK ())
    matchRO ro = if (rkn ro) then [Krules ((length ro)-1)] else []

-- the RKn rule of the K modal logic ------------------------------------------

rkn l =
    case l of
     []                 -> False
     (TVandMA (x,t):[]) -> if t then True else False
     (TVandMA (x,t):tl) -> if t then False else (rkn tl)
