{- |
Module      :  $Header$
Description :  Derive induction schemes from sort generation constraints
Copyright   :  (c) Till Mossakowski and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

Derivation of induction schemes from sort generation constraints.
We provide both second-order induction schemes as well as their
instantiation to specific first-order formulas.
-}

module CASL.Induction where

import CASL.AS_Basic_CASL
import CASL.Fold
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Result


-- | derive a second-order induction scheme from a sort generation constraint
-- | the second-order predicate variables are represented as predicate
-- | symbols P[s], where s is a sort
inductionScheme :: [Constraint] -> Result (FORMULA f)
inductionScheme constrs =
  induction constrs (map predSubst constrs)
  where predSubst constr t =
          Predication predSymb [t] nullRange
          where
          predSymb = Qual_pred_name id typ nullRange
          s = origSort constr
          id = Id [mkSimpleId "P"] [s] nullRange
          typ = Pred_type [newSort constr] nullRange

-- | Function for derivation of first-order instances of sort generation
-- | constraints.
-- | Given a list of formulas with a free sorted variable, instantiate the 
-- | sort generation constraint for this list of formulas
-- | It is assumed that the (original) sorts of the constraint
-- | match the sorts of the free variables
instantiateSortGen :: [Constraint] -> [(FORMULA f,VAR,SORT)] 
                        -> Result (FORMULA f)
instantiateSortGen constrs phis =
  induction constrs (map substFormula phis)
  where substFormula (phi,v,_) t = substitute v t phi

-- | substitute a term for a variable in a formula
substitute :: VAR -> TERM f -> FORMULA f -> FORMULA f
substitute v t = foldFormula $
 (mapRecord id) {foldQual_var = \ t2 v2 s _ ->
                if v == v2 then t else t2 }

-- | derive an induction scheme from a sort generation constraint
-- | using substitutions as induction predicates
induction :: [Constraint] -> [TERM f -> FORMULA f] -> Result (FORMULA f)
induction constrs substs =
  if not (length constrs == length substs)
    then fail "CASL.Induction.induction: argument lists must have equal length"
    else return $
          Implication inductionPremises inductionConclusion True nullRange
  where
  sortInfo = zip3 constrs substs 
                  (zip (map mkVar [1..length constrs]) (map newSort constrs))
  inductionConclusion = mkConj $ map mkConclusion sortInfo
  mkConclusion (_,subst,(v,s)) = 
    Quantification Universal [Var_decl [v] s nullRange] 
                   (subst (var (v,s))) nullRange
  mkVar i = mkSimpleId ("x_"++show i)
  var (v,s) = Qual_var v s nullRange
  inductionPremises = mkConj $ map mkPrem sortInfo

-- | construct a premise for the induction scheme 
-- | (i.e. for one sort in the constraint)
mkPrem :: (Constraint, TERM f -> FORMULA f, (VAR,SORT)) -> FORMULA f
mkPrem (constr,subst,(v,s)) = True_atom nullRange

-- | optimized conjunction
mkConj :: [FORMULA f] -> FORMULA f
mkConj [] = False_atom nullRange
mkConj [phi] = phi
mkConj phis = Conjunction phis nullRange
