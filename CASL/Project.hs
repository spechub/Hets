{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This module replaces Cast(s) with explicit projection
   functions.  Don't do this after simplification since crucial sort
   information may be missing 

   Membership test are replaced with Definedness formulas
-}

module CASL.Project where

import CASL.AS_Basic_CASL
import CASL.Overload
import CASL.Fold
import Common.Id

-- | the name of projections
projName :: Id
projName = mkId [mkSimpleId "g__proj"]

project :: FunKind -> Range -> TERM f -> SORT -> TERM f
project fk pos argument result_type = let argument_type = term_sort argument in
    if argument_type == result_type then argument else 
    Application (projOpSymb fk pos argument_type result_type) 
                    [argument] nullRange

projOpSymb :: FunKind -> Range -> SORT -> SORT -> OP_SYMB
projOpSymb fk pos s1 s2 =
    Qual_op_name projName (Op_type fk [s1] s2 pos) pos

projRecord :: FunKind -> (f -> f) -> Record f (FORMULA f) (TERM f)
projRecord fk mf = (mapRecord mf) 
     { foldCast = \ _ st s ps -> project fk ps st s
     , foldMembership = \ _ t s ps -> Definedness (project fk ps t s) ps
     }

projTerm :: FunKind -> (f -> f) -> TERM f -> TERM f
projTerm fk = foldTerm . projRecord fk

projFormula :: FunKind -> (f -> f) -> FORMULA f -> FORMULA f
projFormula fk = foldFormula . projRecord fk
