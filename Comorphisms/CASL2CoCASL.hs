{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from CASL to ColCASL.

-}

module Comorphisms.CASL2CoCASL where

import Logic.Logic
import Logic.Comorphism
import qualified Common.Lib.Set as Set

-- CASL
import CASL.Logic_CASL 
import CASL.Sublogic
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

-- CoCASLCASL
import CoCASL.Logic_CoCASL
import CoCASL.AS_CoCASL
import CoCASL.CoCASLSign
import CoCASL.StatAna (CSign)

-- | The identity of the comorphism
data CASL2CoCASL = CASL2CoCASL deriving (Show)

instance Language CASL2CoCASL -- default definition is okay

instance Comorphism CASL2CoCASL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               Symbol RawSymbol ()
               CoCASL ()
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign 
               CoCASLMor
               Symbol RawSymbol () where
    sourceLogic CASL2CoCASL = CASL
    sourceSublogic CASL2CoCASL = CASL_SL
                      { has_sub = True, 
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic CASL2CoCASL = CoCASL
    targetSublogic CASL2CoCASL = ()
    map_sign CASL2CoCASL sig = let e = mapSig sig in Just (e, [])
    map_morphism CASL2CoCASL = Just . mapMor
    map_sentence CASL2CoCASL _ = Just . mapSen
    map_symbol CASL2CoCASL = Set.single . mapSym

mapSig :: CASLSign -> CSign
mapSig sign = 
     (emptySign emptyCoCASLSign) {sortSet = sortSet sign
	       , sortRel = sortRel sign
               , opMap = opMap sign
	       , assocOps = assocOps sign
	       , predMap = predMap sign }

mapMor :: CASLMor -> CoCASLMor
mapMor m = Morphism {msource = mapSig $ msource m
	           , mtarget = mapSig $ mtarget m
                   , sort_map = sort_map m
                   , fun_map = fun_map m
                   , pred_map = pred_map m
	           , extended_map = ()}


mapSym :: Symbol -> Symbol
mapSym = id  -- needs to be changed once CoCASL symbols are added


mapSen :: CASLFORMULA -> CoCASLFORMULA
mapSen f = case f of 
    Quantification q vs frm ps ->
	Quantification q vs (mapSen frm) ps
    Conjunction fs ps -> 
        Conjunction (map mapSen fs) ps 
    Disjunction fs ps -> 
        Disjunction (map mapSen fs) ps
    Implication f1 f2 b ps ->
	Implication (mapSen f1) (mapSen f2) b ps
    Equivalence f1 f2 ps -> 
	Equivalence (mapSen f1) (mapSen f2) ps
    Negation frm ps -> Negation (mapSen frm) ps
    True_atom ps -> True_atom ps
    False_atom ps -> False_atom ps
    Existl_equation t1 t2 ps -> 
	Existl_equation (mapTERM t1) (mapTERM t2) ps
    Strong_equation t1 t2 ps -> 
	Strong_equation (mapTERM t1) (mapTERM t2) ps
    Predication pn as qs ->
        Predication pn (map mapTERM as) qs
    Definedness t ps -> Definedness (mapTERM t) ps
    Membership t ty ps -> Membership (mapTERM t) ty ps
    Sort_gen_ax constrs isFree -> Sort_gen_ax constrs isFree
    _ -> error "CASL2CoCASL.mapSen"

mapTERM :: TERM () -> TERM C_FORMULA
mapTERM t = case t of
    Qual_var v ty ps -> Qual_var v ty ps
    Application opsym as qs  -> Application opsym (map mapTERM as) qs
    Sorted_term trm ty ps -> Sorted_term (mapTERM trm) ty ps 
    Cast trm ty ps -> Cast (mapTERM trm) ty ps 
    Conditional t1 f t2 ps -> 
       Conditional (mapTERM t1) (mapSen f) (mapTERM t2) ps
    _ -> error "CASL2CoCASL.mapTERM"
