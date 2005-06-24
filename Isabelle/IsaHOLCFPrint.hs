{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  portable

Printing functions for Isabelle logic.
-}

module Isabelle.IsaHOLCFPrint where

import Isabelle.IsaPrint as IsaPrint
import Isabelle.IsaSign 
import Isabelle.IsaConsts
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import Common.AS_Annotation
import Data.Char
import qualified Common.Lib.Map as Map

------------------- Printing functions -------------------


-- omits type of outer abstraction
showOUTerm :: Term -> String
showOUTerm t = case t of
  (Abs v y tm l) -> lb ++ (case l of 
     NotCont -> "%"
     IsCont -> "LAM ") ++ showTerm v ++ ". " ++ showOUTerm tm ++ rb
  _ -> showTerm t


{-
showClassrel :: TSig -> Doc
showClassrel tysig =  if Map.null (classrel tysig) then empty
      else text $ Map.foldWithKey showTycon "" (classrel tysig) 
  where showTycon t cl rest =
    if null cl then empty
    else  "axclass " ++ classId t ++ " < " (if cl == [] then "pcpo" 
      else showSort cl)

showArities :: TSig -> Doc
showArities tysig =  if Map.null (arities tysig) then empty  
      else text $ Map.foldWithKey showTycon "" (arities tysig) 
  where 
   showInstances t cl rest =
     if null cl then empty
     else map (showInstance t) cl
   showInstance t xs = "instance " ++ (show t) ++ " :: " ++ "(" ++ (showClass $ snd cl) ++ ") " ++ classId $ fst cl

instance PrettyPrint TypeSig where
  printText0 _ tysig =    if Map.null (arities tysig) then empty
      else text $ Map.foldWithKey showTycon "" (arities tysig) 
    where showTycon t arity' rest = 
              let arity = if null arity' then
                          error "IsaPrint.printText0 (TypeSig)" 
                                else length (snd $ head arity') in 
            "typedecl "++
            (if arity>0 then lb++concat (map ((" 'a"++).show) [1..arity])++rb
             else "") ++ show t  ++"\n"++rest
-}


