{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

module to store utillities for CASL and ist Comorphisms

-}

module CASL.Utils where

import Maybe (isJust,fromJust)

import CASL.AS_Basic_CASL

-- |
-- replacePropPredication replaces a propositional predication of a
-- given symbol with an also given Formula. Optionally a given variable
-- is replaced in the predication of another predicate symbol with a
-- given term, the variable must occur in the first argument position
-- of the predication.

replacePropPredication :: Maybe (PRED_NAME,VAR,TERM f) 
                        -- ^ Just (pSymb,x,t) replace x 
			-- with t in Predication of pSymb 
                       -> PRED_NAME -- ^ propositional symbol to replace
		       -> FORMULA f -- ^ Formula to insert
		       -> FORMULA f -- ^ Formula with placeholder
		       -> FORMULA f
replacePropPredication mTerm pSymb frmIns frmToChn =
    case frmToChn of
    Quantification q vs frm ps ->
	Quantification q vs (replacePropPredication mTerm pSymb frmIns frm) ps
    Conjunction fs ps -> 
	Conjunction (map (replacePropPredication mTerm pSymb frmIns) fs) ps 
    Implication f1 f2 b ps ->
	Implication (replacePropPredication mTerm pSymb frmIns f1) 
		    (replacePropPredication mTerm pSymb frmIns f2) b ps
    Predication (Qual_pred_name symb (Pred_type [] []) []) [] [] 
	| symb == pSymb -> frmIns
    Predication qpn@(Qual_pred_name symb _ _) (arg1:args) ps
	| (isJust mTerm) && symb == pSymbT -> 
	    case arg1 of
	    Sorted_term (Qual_var v1 _ _) _ _ 
		| v1 == var -> Predication qpn (term:args) ps 
	    _ -> error "Modal2CASL: replacePropPredication: unknown term to replace"
          where (pSymbT,var,term) = fromJust mTerm 
    p@(Predication _ _ _) -> p 
    _ -> error "Modal2CASL: replacePropPredication: unknown formula to replace"

-- | 
-- noMixfixF checks a 'FORMULA' f for Mixfix_*. A logic specific helper has to be provided for checking the 'f'.

noMixfixF :: (Show f) => (f -> Bool) -> FORMULA f -> Bool
noMixfixF cef form = 
    let rec = noMixfixF cef 
	tchk = noMixfixT cef
    in
    case form of
    ExtFORMULA f -> cef f
    Quantification _ _ f _ -> rec f
    Conjunction fs _ -> and $ map rec fs
    Disjunction fs _ -> and $ map rec fs
    Implication f1 f2 _ _ -> rec f1 && rec f2
    Equivalence f1 f2 _   -> rec f1 && rec f2
    Negation f _ -> rec f
    Predication _ ts _  -> and $ map tchk ts
    Definedness t _ -> tchk t
    Existl_equation t1 t2 _ -> tchk t1 && tchk t2
    Strong_equation t1 t2 _ -> tchk t1 && tchk t2
    Membership t _ _ -> tchk t
    Mixfix_formula _ -> False
    Unparsed_formula _ _ -> error ("CASL.Utils.noMixfixF: should not occur: "
				   ++show form)
    _ -> True -- {True,False}_atom

-- | 
-- noMixfixT checks a 'TERM' f for Mixfix_*. A logic specific helper has to be provided for checking the 'f'.
    
noMixfixT :: (Show f) => (f -> Bool) -> TERM f -> Bool
noMixfixT cef term = 
    let fchk = noMixfixF cef 
	tchk = noMixfixT cef
    in
    case term of
    Simple_id _ -> True
    Qual_var _ _ _ -> True
    Application _ ts _ -> and $ map tchk ts
    Sorted_term t _ _  -> tchk t
    Cast t _ _ -> tchk t
    Conditional t1 f t2 _ -> tchk t1 && fchk f && tchk t2
    Unparsed_term _ _ -> error ("CASL.Utils.noMixfixT: should not occur: "
				   ++show term)
    _ -> False