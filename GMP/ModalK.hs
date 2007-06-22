{-# OPTIONS -fglasgow-exts #-}
module ModalK where

import GMPAS
import ModalLogic

instance ModalLogic ModalK Krules where   
    parseIndex = return (ModalK ())
    matchRO ro = if (rkn ro) then [KR ((length ro)-1)] else []

-- the RKn rule of the K modal logic ------------------------------------------
rkn :: [TVandMA t] -> Bool
rkn l =
    case l of
     []                 -> False
     (TVandMA (_,t):[]) -> if t then True else False
     (TVandMA (_,t):tl) -> if t then False else (rkn tl)
