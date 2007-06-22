{-# OPTIONS -fglasgow-exts #-}
module ModalKD where

import GMPAS
import ModalLogic

instance ModalLogic ModalKD KDrules where
    parseIndex = return (ModalKD ())
    matchRO ro = if (rkn ro)&&(rule2 ro)
                  then [KDPR ((length ro)-1), KDNR (length ro)]
                  else if (rkn ro)
                        then [KDPR ((length ro)-1)]
                        else if (rule2 ro)
                              then [KDNR (length ro)]
                              else []
-- the RKn rule of the KD modal logic -----------------------------------------
rkn :: [TVandMA t] -> Bool
rkn l =
    case l of
     []                 -> False
     (TVandMA (_,t):[]) -> if t then True else False
     (TVandMA (_,t):tl) -> if t then False else (rkn tl)
-- the ??? rule of the KD modal logic -----------------------------------------
rule2 :: [TVandMA t] -> Bool
rule2 l =
    case l of
     []                 -> True
     (TVandMA (_,t):tl) -> if t then (rule2 tl) else False
