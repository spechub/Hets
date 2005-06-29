{-# OPTIONS -cpp #-}
{-| 
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

dumping a LibEnv to Isabelle theory files
-}

module Isabelle.CreateThy where

import Data.List

import Common.AS_Annotation
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.PrettyPrint
import Common.PPUtils
import Common.Lib.Pretty as P

import Isabelle.IsaSign as IsaSign
import Isabelle.Translate
import Isabelle.IsaPrint
import Isabelle.IsaHOLCFPrint 


createTheoryText :: Sign -> [Named Sentence] -> Doc
createTheoryText sig sens =
    let (axs, rest) = getAxioms sens
        (defs, _) = getDefs rest
    in printText sig $++$
    (if null axs then empty else text "axioms" $$ 
        vcat (map printNamedSen $ disambiguate sig axs)) $++$
    (if null defs then empty else text "defs" $$
        vcat (map printNamedSen defs)) 
    $++$ text "end"     

getAxioms, getDefs :: [Named Sentence] -> 
                 ([Named Sentence], [Named Sentence])
getAxioms = partition ( \ s -> case sentence s of 
                            Sentence _ -> True
                            _ -> False)

getDefs = partition ( \ s -> case sentence s of 
                            ConstDef _ -> True
                            _ -> False)

disambiguate :: Sign -> [Named Sentence] -> [Named Sentence]
disambiguate sign axs = 
    let s0 = Map.findWithDefault Set.empty (baseSig sign) isaPrelude
        number :: Set.Set String -> Int -> String -> String
        number given c n = let new = n ++ show c in 
                               if Set.member new given then 
                                  number given (c+1) n else new
        rename given n = if Set.member n given then number given 2 n else n
        accFun s a = let m = senName a
                         n = if null m then number s 1 "Ax" 
                                 else rename s (transString m) 
                     in (Set.insert n s, a { senName = n})
     in snd $ mapAccumL accFun s0 axs

printNamedSen :: Named Sentence -> Doc
printNamedSen (NamedSen lab _ s) = text (case s of
    ConstDef _ -> lab ++ "_def"
    Sentence _ -> lab
    Theorem _ _ _ -> "theorem " ++ lab) 
    <+> colon <+> doubleQuotes (case senTerm s of
      IsaEq (Const df y) t ->  
        (text df) <+> text "::" <+> text (showTyp Unquoted 1000 y) <+> text "==" 
                    <+> text (showOUTerm t)
      _ -> (printText s)) <> text "\n"

