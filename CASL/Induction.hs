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
          predSymb = Qual_pred_name ident typ nullRange
          s = origSort constr
          ident = Id [mkSimpleId "P"] [s] nullRange
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
 (mapRecord id) {foldQual_var = \ t2 v2 _ _ ->
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
  mkConclusion (_,subst,v) = 
    Quantification Universal [mkVarDecl v] (subst (var v)) nullRange
  mkVar i = mkSimpleId ("x_"++show i)
  var (v,s) = Qual_var v s nullRange
  inductionPremises = mkConj $ concatMap mkPrems sortInfo

-- | construct premise set for the induction scheme 
-- | for one sort in the constraint
mkPrems :: (Constraint, TERM f -> FORMULA f, (VAR,SORT)) -> [FORMULA f]
mkPrems info@(constr,_,_) = map (mkPrem info) (opSymbs constr)

-- | construct a premise for the induction scheme for one constructor
mkPrem :: (Constraint, TERM f -> FORMULA f, (VAR,SORT)) -> (OP_SYMB,[Int])
          -> FORMULA f
mkPrem (constr,subst,(v,s)) 
       (Qual_op_name op (Op_type _ argTypes resType _) _, idx) = 
  if null vars then phi
     else Quantification Universal (map mkVarDecl qVars) phi nullRange
  where
  vars = map mkVar [1..length argTypes]
  mkVar i = mkSimpleId ("y_"++show i)
  qVars = zip vars argTypes  
  phi = if null vars then undefined else undefined
mkPrem _ (opSym,_) = 
  error ("CASL.Induction. mkPrems: unqualified operation symbol occuring in constraint: "++ show opSym)

-- | turn sorted variable into variable delcaration
mkVarDecl :: (VAR,SORT) -> VAR_DECL
mkVarDecl (v,s) = Var_decl [v] s nullRange

-- | optimized conjunction
mkConj :: [FORMULA f] -> FORMULA f
mkConj [] = False_atom nullRange
mkConj [phi] = phi
mkConj phis = Conjunction phis nullRange
