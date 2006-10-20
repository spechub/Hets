{- |
Module      :  $Header$
Description :  Derive induction schemes from sort generation constraints
Copyright   :  (c) Till Mossakowski and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
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
inductionScheme :: [Constraint] -> FORMULA f
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
instantiateSortGen :: [Constraint] -> [(FORMULA f,VAR,SORT)] -> FORMULA f
instantiateSortGen constrs phis =
  induction constrs (map substFormula phis)
  where substFormula (phi,v,_) t = substitute v t phi

substitute :: VAR -> TERM f -> FORMULA f -> FORMULA f
substitute v t = foldFormula $
 (mapRecord id) {foldQual_var = \ t2 v2 s _ ->
                if v == v2 then t else t2 }

-- | derive an induction scheme from a sort generation constraint
-- | using substitutions as induction predicates
induction :: [Constraint] -> [TERM f -> FORMULA f] -> FORMULA f
induction constrs subst =
  Implication inductionPremises inductionConclusion True nullRange
  where
  inductionConclusion = True_atom nullRange -- Quantification Universal [Var_decl [v] s nullRange] phi
  inductionPremises = True_atom nullRange