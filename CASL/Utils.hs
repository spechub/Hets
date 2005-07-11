{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich and Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

module to store utilities for CASL and its comorphisms

-}

module CASL.Utils where

import Control.Exception (assert)

import Data.Maybe (isJust,fromJust)
import Data.List
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map

import Common.Id
import CASL.AS_Basic_CASL
import CASL.Fold

-- |
-- replacePropPredication replaces a propositional predication of a
-- given symbol with an also given formula. Optionally a given variable
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
replacePropPredication mTerm pSymb frmIns =
    foldFormula (mapRecord $ const $ error 
             "replacePropPredication: unexpected extended formula")
        { foldPredication = \ (Predication qpn ts ps) _ _ _ -> 
              let (pSymbT,var,term) = fromJust mTerm in case qpn of
              Qual_pred_name symb (Pred_type s _) _ 
                 | symb == pSymb && null ts && null s -> frmIns
                 | isJust mTerm && symb == pSymbT -> case ts of
                   Sorted_term (Qual_var v1 _ _) _ _ : args 
                       |  v1 == var -> Predication qpn (term:args) ps 
	           _ -> error "replacePropPredication: unknown term to replace"
              _ -> error "replacePropPredication: unknown formula to replace"
         , foldConditional = \ t _ _ _ _ -> t }

-- | 
-- noMixfixF checks a 'FORMULA' f for Mixfix_*. 
-- A logic specific helper has to be provided for checking the f.
noMixfixF :: (f -> Bool) -> FORMULA f -> Bool
noMixfixF = foldFormula . noMixfixRecord

-- | 
-- noMixfixT checks a 'TERM' f for Mixfix_*. 
-- A logic specific helper has to be provided for checking the f.
noMixfixT :: (f -> Bool) -> TERM f -> Bool
noMixfixT = foldTerm . noMixfixRecord

-- |
-- isMixfixTerm checks the 'TERM' f for Mixfix_*, 
-- but performs no recusive lookup
isMixfixTerm :: TERM f -> Bool
isMixfixTerm term =
    case term of
    Simple_id _ -> False -- error "CASL.Utils.isMixfixTerm"
    Qual_var _ _ _ -> False
    Application _ _ _ -> False
    Sorted_term _ _ _  -> False
    Cast _ _ _ -> False
    Conditional _ _ _ _ -> False
    Unparsed_term s _ -> 
        error $ "CASL.Utils.isMixfixTerm: should not occur: " ++ s
    _ -> True

type FreshVARMap f = Map.Map VAR (TERM f)

-- | build_vMap constructs a mapping between a list of old variables and
-- corresponding fresh variables based on two lists of VAR_DECL
build_vMap :: [VAR_DECL] -> [VAR_DECL] -> FreshVARMap f
build_vMap vDecls f_vDecls = 
    Map.fromList (concat (zipWith toTups vDecls f_vDecls))
    where toTups (Var_decl vars1 sor1 _) (Var_decl vars2 sor2 _) =
              assert (sor1 == sor2)
                     (zipWith (toTup sor1) vars1 vars2)
          toTup s v1 v2 = (v1,toVarTerm v2 s)

-- | specialised lookup in FreshVARMap that ensures that the VAR with
-- the correct type (SORT) is replaced
lookup_vMap :: VAR -> SORT -> FreshVARMap f -> Maybe (TERM f)
lookup_vMap v s m = 
    maybe Nothing 
          (\ t@(Qual_var _ s' _) -> if s==s' then Just t else Nothing) 
          (Map.lookup v m)

-- | specialized delete that deletes all shadowed variables
delete_vMap :: [VAR_DECL] -> FreshVARMap f-> FreshVARMap f
delete_vMap vDecls m = foldr Map.delete m vars
    where vars = concatMap (\ (Var_decl vs _ _) -> vs) vDecls

-- | replace_vars replaces all Qual_var occurences that are sopposed
-- to be replaced according to the FreshVARMap
replace_vars :: FreshVARMap f
             -> (FreshVARMap f -> f -> f) 
             -- ^ this function replaces Qual_var in ExtFORMULA 
             -> FORMULA f -> FORMULA f
replace_vars m rep_ef phi =
    case phi of
    ExtFORMULA f -> ExtFORMULA (rep_ef m f)
    Quantification q vs f ps -> 
        let new_map = delete_vMap vs m
        in Quantification q vs (if Map.null new_map 
                                   then f
                                   else replace_vars new_map rep_ef f) ps
    Conjunction fs ps -> Conjunction (map rec fs) ps
    Disjunction fs ps -> Disjunction (map rec fs) ps
    Implication f1 f2 b ps -> Implication (rec f1) (rec f2) b ps
    Equivalence f1 f2 ps   -> Equivalence (rec f1) (rec f2) ps
    Negation f ps -> Negation (rec f) ps
    Predication symb ts ps  -> Predication symb (map recT ts) ps
    Definedness t ps -> Definedness (recT t) ps
    Existl_equation t1 t2 ps -> Existl_equation (recT t1) (recT t2) ps
    Strong_equation t1 t2 ps -> Strong_equation (recT t1) (recT t2) ps
    Membership t s ps -> Membership (recT t) s ps
    Mixfix_formula _ -> err "Mixfix_formula"
    Unparsed_formula _ _ -> err "Unparsed_formula"
    f -> f -- (True_atom and False_atom)
    where rec = replace_vars m rep_ef
          recT = replace_varsT m rep_ef
          err s = error ("CASL.Utils.replace_vars: cannot handle "++s)
    
replace_varsT :: FreshVARMap f
              -> (FreshVARMap f -> f -> f) 
              -- ^ this function replaces Qual_var in ExtFORMULA 
              -> TERM f -> TERM f 
replace_varsT m rep_ef term =
    case term of
    si@(Simple_id _) -> si
    q@(Qual_var v s _) -> maybe q id (lookup_vMap v s m)
    Application symb ts ps -> Application symb (map recT ts) ps
    Sorted_term t s ps  -> Sorted_term (recT t) s ps
    Cast t s ps -> Cast (recT t) s ps
    Conditional t1 f t2 ps -> Conditional (recT t1) (rec f) (recT t2) ps
    Unparsed_term _ _ -> err "Unparsed_term"
    _ -> err "Mixfix_*"
    where err s = error ("CASL.Utils.replace_varsT: should not occur: "++s)
          rec = replace_vars m rep_ef
          recT = replace_varsT m rep_ef

-- | codeOutUniqueExt compiles every unique_existential quantification
-- to simple quantifications. It works recursively through the whole
-- formula and only touches Unique_existential quantifications
codeOutUniqueExt :: (f -> f) 
                    -- ^ codes out Unique_existential in ExtFORMULA
                 -> (FreshVARMap f -> f -> f) 
                 -- ^ this function replaces Qual_var in ExtFORMULA 
                 -> FORMULA f -> FORMULA f
codeOutUniqueExt pr_ef rep_ef phi =
    case phi of
    Quantification Unique_existential vDecl f _ -> 
        let f' = rec f
            vDecl' = fresh_vars vDecl
            f'_rep = replace_vars (build_vMap vDecl vDecl') rep_ef f'
            allForm = Quantification Universal vDecl' 
                           (Implication f'_rep implForm True []) []
            implForm = assert (not (null vDecl))
                       (let fs = concat (zipWith eqForms vDecl vDecl')
                        in (if length fs == 1 
                               then head fs
                               else Conjunction fs []))
        in Quantification Existential 
                   vDecl (Conjunction [f',allForm] []) []
    ExtFORMULA f -> ExtFORMULA (pr_ef f)
    Quantification q vs f ps -> Quantification q vs (rec f) ps
    Conjunction fs ps -> Conjunction (map rec fs) ps
    Disjunction fs ps -> Disjunction (map rec fs) ps
    Implication f1 f2 b ps -> Implication (rec f1) (rec f2) b ps
    Equivalence f1 f2 ps   -> Equivalence (rec f1) (rec f2) ps
    Negation f ps -> Negation (rec f) ps
    Predication symb ts ps  -> Predication symb (map recT ts) ps
    Definedness t ps -> Definedness (recT t) ps
    Existl_equation t1 t2 ps -> Existl_equation (recT t1) (recT t2) ps
    Strong_equation t1 t2 ps -> Strong_equation (recT t1) (recT t2) ps
    Membership t s ps -> Membership (recT t) s ps
    Mixfix_formula _ -> err "Mixfix_formula"
    Unparsed_formula _ _ -> err "Unparsed_formula"
    f -> f -- (True_atom and False_atom)
    where rec = codeOutUniqueExt pr_ef rep_ef
          recT = codeOutUniqueExtT pr_ef rep_ef
          err s = error ("CASL.Utils.codeOutUniqueExt: cannot handle "++s)
          eqForms (Var_decl vars1 sor1 _) (Var_decl vars2 sor2 _) =
              assert (sor1 == sor2)
                     (zipWith (eqFor sor1) vars1 vars2)
          eqFor s v1 v2 = Strong_equation (toSortTerm (toVarTerm v1 s))
                                          (toSortTerm (toVarTerm v2 s))
                                          []
          fresh_vars = snd . mapAccumL fresh_var Set.empty
          fresh_var accSet (Var_decl vars sor _) = 
              let accSet' = Set.union (Set.fromList vars) accSet
                  (accSet'',vars') = mapAccumL nVar accSet' vars
              in (accSet'',Var_decl vars' sor [])
          genVar t i = Token (tokStr t ++ '_':show i) nullPos
          nVar aSet v = 
              let v' = fromJust (find (not . flip Set.member aSet) 
                                 ([genVar v (i :: Int) | i<-[1..]]))
              in (Set.insert v' aSet,v')

codeOutUniqueExtT :: (f -> f) 
                  -- ^ codes out Unique_existential in ExtFORMULA
                  -> (FreshVARMap f -> f -> f) 
                  -- ^ this function replaces Qual_var in ExtFORMULA 
                  -> TERM f -> TERM f 
codeOutUniqueExtT pr_ef rep_ef term =
    case term of
    si@(Simple_id _) -> si
    q@(Qual_var _ _ _) -> q
    Application symb ts ps -> Application symb (map recT ts) ps
    Sorted_term t s ps  -> Sorted_term (recT t) s ps
    Cast t s ps -> Cast (recT t) s ps
    Conditional t1 f t2 ps -> Conditional (recT t1) (rec f) (recT t2) ps
    Unparsed_term _ _ -> err "Unparsed_term"
    _ -> err "Mixfix_*"
    where err s = error ("CASL.Utils.codeOutUniqueExtT: should not occur: "++s)
          rec = codeOutUniqueExt pr_ef rep_ef
          recT = codeOutUniqueExtT pr_ef rep_ef


-- | adds Sorted_term to a Qual_var term
toSortTerm :: TERM f -> TERM f
toSortTerm t@(Qual_var _ s _) = Sorted_term t s []
toSortTerm _ = error "CASL2TopSort.toSortTerm: can only handle Qual_var" 

-- | generates from a variable and sort an Qual_var term
toVarTerm :: VAR -> SORT -> TERM f
toVarTerm vs s = (Qual_var vs s [])
