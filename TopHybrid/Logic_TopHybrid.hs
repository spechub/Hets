{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
             UndecidableInstances, ExistentialQuantification #-}
{- |
Module      :  ./TopHybrid/Logic_TopHybrid.hs
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  : nevrenato@gmail.com
Stability   : experimental
Portability : portable

Description :
Instance of class Logic for hybridized logics
with an arbitrary logic under.
-}
module TopHybrid.Logic_TopHybrid where

import qualified Data.Map as M
import Logic.Logic
import TopHybrid.AS_TopHybrid
import TopHybrid.TopHybridSign
import TopHybrid.Parse_AS
import TopHybrid.Print_AS
import TopHybrid.StatAna
import TopHybrid.Utilities
import CASL.Morphism
import CASL.AS_Basic_CASL
import CASL.Sign

-- Import of logics
import CASL.Logic_CASL
import Propositional.Logic_Propositional
import CoCASL.Logic_CoCASL
-- End of import of logics

data Hybridize = Hybridize deriving Show

instance Language Hybridize where
 description _ = "Hybridization of an arbitrary logic"

instance Category Sgn_Wrap Mor where
 ide = undefined
 inverse = undefined
 composeMorphisms = undefined
 dom = undefined
 cod = undefined
 isInclusion = undefined
 legal_mor = undefined

instance Syntax Hybridize Spc_Wrap Symbol SYMB_ITEMS SYMB_MAP_ITEMS where
        parse_basic_spec Hybridize = Just $ \ _ -> thBasic getLogic
        parse_symb_items Hybridize = Just . const $ error "parse_symb_items !"
        parse_symb_map_items Hybridize = Just . const $ error "parse_symb_map_items !"
        toItem Hybridize = error "toItem !"

instance Sentences Hybridize Frm_Wrap Sgn_Wrap Mor Symbol where
        map_sen Hybridize = error "map_sen !"
        negation Hybridize = error "negation !"
        sym_of Hybridize = error "sym_of !"
        mostSymsOf Hybridize = error "mostSymsOf !"
        symmap_of Hybridize = error "symmap_of !"
        sym_name Hybridize = error "sym_name !"
        symKind Hybridize = error "symKind !"
        symsOfSen Hybridize = error "symsOfSen !"
        simplify_sen Hybridize = simSen
        print_named Hybridize = printNamedFormula

instance StaticAnalysis Hybridize Spc_Wrap Frm_Wrap SYMB_ITEMS SYMB_MAP_ITEMS
          Sgn_Wrap Mor Symbol RawSymbol where
                basic_analysis Hybridize = Just thAna
                empty_signature Hybridize = emptyHybridSign
                sen_analysis Hybridize = Just anaForm'
                stat_symb_map_items Hybridize = error "stat_symb_map_items !"
                stat_symb_items Hybridize = error "stat_symb_items !"
                signature_colimit Hybridize = error "signature_colimit !"
                quotient_term_algebra Hybridize =
                 error "quotient_term_algebra !"
                ensures_amalgamability Hybridize =
                 error "ensures_amalgamability !"
                qualify Hybridize = error "qualify !"
                symbol_to_raw Hybridize = error "symbol_to_raw !"
                matches Hybridize = error "matches !"
                is_transportable Hybridize = error "is_transportable !"
                is_injective Hybridize = error "is_injective !"
                add_symb_to_sign Hybridize = error "add_symb_to_sign !"
                signature_union Hybridize = error "signature_union !"
                signatureDiff Hybridize = sgnDiff
                intersection Hybridize = error "intersection !"
                morphism_union Hybridize = error "morphism_union !"
                final_union Hybridize = error "final_union !"
                is_subsig Hybridize = isSubTHybSgn
                subsig_inclusion Hybridize = error "sub_sig_inclusion !"
                cogenerated_sign Hybridize = error "cogenerated_sign !"
                generated_sign Hybridize = error "generated_sign !"
                induced_from_morphism Hybridize =
                 error "induced_from_morphism !"
                induced_from_to_morphism Hybridize =
                 error "induced_from_to_morphism !"
                theory_to_taxonomy Hybridize = error "theory_to_taxonomy !"

instance Logic Hybridize () Spc_Wrap Frm_Wrap SYMB_ITEMS SYMB_MAP_ITEMS
               Sgn_Wrap Mor Symbol RawSymbol () where
                stability Hybridize = Experimental
                parse_basic_sen Hybridize = Just formParser'
                proj_sublogic_epsilon Hybridize =
                 error "proj_sublogic_epsilon !"
                empty_proof_tree Hybridize = error "empty_proof_tree !"
                addOMadtToTheory Hybridize = error "addOMadtToTheory !"
                addOmdocToTheory Hybridize = error "addOmdocToTheory !"
                syntaxTable Hybridize = error "syntaxTable !"
                provers Hybridize = []
{- --- The logics supported section ----
Logics supported -}
underlogicList :: [(String, AnyLogic)]
underlogicList = [
                   (show CASL, Logic CASL),
                   (show Propositional, Logic Propositional),
                   (show CoCASL, Logic CoCASL),
                   (show Hybridize, Logic Hybridize)
                 ]

-- Construction of the underlogics map using a list
underlogics :: M.Map String AnyLogic
underlogics = buildMapFromList underlogicList

{- Tries to get a logic, if it fails, then
gives an error saying that the logic in question doesn't exist -}
getLogic :: String -> AnyLogic
getLogic s = maybeE 3 $ M.lookup s underlogics
