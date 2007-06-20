module ModalK where

import GMPAS
import ModalLogic
import GMPSAT

instance ModalLogic ModalK where   
    parseIndex = return (ModalK ())
{-
instance ModalLogic ModalK where
    matchRO f =
     let sl = genPV f
         ll = genAllLists sl
     in match ll
-- the RKn rule ok the K modal logic -------------------------------------------
RKn l =
    case l of
     []                 -> False
     (TVandMA (x,t):[]) -> if t then True else False
     (TVandMA (x,t):tl) -> if t then False else (RKn tl)
-- return the first encountered matching list if any found ----------------------
match l =
    case l of
     [] -> []
     _  -> let aux = head l
               t = RKn aux
           in if t
               then aux
               else match (tail l)
-}
