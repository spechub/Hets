{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  Free variables; getting rid of superfluous quantifications
    
-}
module CASL.Quantification where

import CASL.AS_Basic_CASL
import Common.Id

-- Free variables

flatVAR_DECL :: VAR_DECL -> [(VAR, SORT)]
flatVAR_DECL (Var_decl vlist s _) = map (\v -> (v,s)) vlist

flatVAR_DECLs :: [VAR_DECL] -> [(VAR, SORT)]
flatVAR_DECLs = concat . map flatVAR_DECL

isFree :: VAR -> FORMULA -> Bool
isFree v (Quantification _ vdecl phi _) =
  not (v `elem` (map fst $ flatVAR_DECLs vdecl))
  && isFree v phi
isFree v (Conjunction phis _) =
  any (isFree v) phis
isFree v (Disjunction phis _) =
  any (isFree v) phis
isFree v (Implication phi1 phi2 _) =
  isFree v phi1 || isFree v phi2
isFree v (Equivalence phi1 phi2 _) =
  isFree v phi1 || isFree v phi2
isFree v (Negation phi _) =
  isFree v phi
isFree v (True_atom _) =
  False
isFree v (False_atom _) =
  False
isFree v (Predication _ args _) =
  any (isFreeInTerm v) args
isFree v (Definedness t _) =
  isFreeInTerm v t
isFree v (Existl_equation t1 t2 _) =
  isFreeInTerm v t1 || isFreeInTerm v t2
isFree v (Strong_equation t1 t2 _) =
  isFreeInTerm v t1 || isFreeInTerm v t2
isFree v (Membership t s _) =
  isFreeInTerm v t
isFree v (Sort_gen_ax sorts ops) =
  False
isFree v (Mixfix_formula _) = 
  False
isFree v (Unparsed_formula _ _) = 
  False

isFreeInTerm :: VAR -> TERM -> Bool
isFreeInTerm v (Qual_var v1 s _) = v==v1
isFreeInTerm v (Application _ args _) =
  any (isFreeInTerm v) args
isFreeInTerm v (Sorted_term t s _) =
  isFreeInTerm v t
isFreeInTerm v (Cast t s _) =
  isFreeInTerm v t
isFreeInTerm v (Conditional t1 phi t2 _) =
  isFree v phi || isFreeInTerm v t1 || isFreeInTerm v t2
isFreeInTerm v (Simple_id v1) = v==v1
isFreeInTerm v (Unparsed_term _ _) = False
isFreeInTerm v (Mixfix_qual_pred _) = False
isFreeInTerm v (Mixfix_term _) = False
isFreeInTerm v (Mixfix_token _) = False
isFreeInTerm v (Mixfix_sorted_term _ _) = False


-- quantify only over free variables
effQuantify :: QUANTIFIER -> [VAR_DECL] -> FORMULA -> [Pos] -> FORMULA
effQuantify q vdecl phi pos =
  if null vdecl'' then phi
     else Quantification q vdecl' phi pos
  where
  filterVAR_DECL phi (Var_decl vs s pos) =
    Var_decl (filter (flip isFree phi) vs) s pos
  vdecl' = map (filterVAR_DECL phi) vdecl
  vdecl'' = flatVAR_DECLs vdecl'

-- strip superfluous quantifications
stripQuant :: FORMULA -> FORMULA
stripQuant (Quantification quant vdecl phi pos) =
  effQuantify quant vdecl phi pos
stripQuant (Conjunction phis pos) =
  Conjunction (map stripQuant phis) pos
stripQuant (Disjunction phis pos) =
  Disjunction (map stripQuant phis) pos
stripQuant (Implication phi1 phi2 pos) =
  Implication (stripQuant phi1) (stripQuant phi2) pos
stripQuant (Equivalence phi1 phi2 pos) =
  Equivalence (stripQuant phi1) (stripQuant phi2) pos
stripQuant (Negation phi pos) =
  Negation (stripQuant phi) pos
stripQuant phi = phi
