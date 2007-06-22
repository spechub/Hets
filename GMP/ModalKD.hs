{-# OPTIONS -fglasgow-exts #-}
module ModalKD where

import GMPAS
import ModalLogic

instance ModalLogic ModalKD KDrules where
    parseIndex = return (ModalKD ())
    matchRO ro = if (rkn ro)
                  then [KDPR ((length ro)-1)]
                  else if (nrkn ro)
                        then [KDNR (length ro)]
                        else []
-- the RKn rule of the KD modal logic -----------------------------------------
rkn :: [TVandMA t] -> Bool
rkn l =
    case l of
     []                 -> False
     (TVandMA (_,t):[]) -> if t then True else False
     (TVandMA (_,t):tl) -> if t then False else (rkn tl)
-- the Negative RKn rule of the KD modal logic --------------------------------
nrkn :: [TVandMA t] -> Bool
nrkn l =
    case l of
     []                 -> True
     (TVandMA (_,t):tl) -> if not(t) then (nrkn tl) else False
