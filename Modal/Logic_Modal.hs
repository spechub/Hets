{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Instance of class Logic for modal logic.
-}

{- todo:
   check preservation of rigidity of morphisms
-}

module Modal.Logic_Modal where

import Modal.AS_Modal
import Modal.ModalSign
import Modal.ATC_Modal
import Modal.Parse_AS
import Modal.StatAna
import Modal.LaTeX_Modal
import CASL.Sign
import CASL.StaticAna
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.MapSentence
import CASL.SymbolParser
import Logic.Logic
import Data.Dynamic
import Common.DynamicUtils
 
import CASL.SimplifySen
import Common.Result

data Modal = Modal deriving Show

instance Language Modal  where
 description _ = 
  "ModalCASL extends CASL by modal operators. Syntax for ordinary\n\ 
  \modalities, multi-modal logics as well as  term-modal\n\ 
  \logic (also covering dynamic logic) is provided.\n\ 
  \Specific modal logics can be obtained via restrictions to\n\ 
  \sublanguages."

type MSign = Sign M_FORMULA ModalSign
type ModalMor = Morphism M_FORMULA ModalSign ()
type ModalFORMULA = FORMULA M_FORMULA

tc_M_FORMULA, tc_M_SIG_ITEM, tc_M_BASIC_ITEM, modalSignTc :: TyCon
tc_M_FORMULA     = mkTyCon "Modal.AS_Modal.M_FORMULA"
tc_M_SIG_ITEM    = mkTyCon "Modal.AS_Modal.M_SIG_ITEM"
tc_M_BASIC_ITEM  = mkTyCon "Modal.AS_Modal.M_BASIC_ITEM"
modalSignTc      = mkTyCon "Modal.ModalSign.ModalSign"

instance Typeable M_FORMULA where
  typeOf _ = mkTyConApp tc_M_FORMULA []
instance Typeable M_SIG_ITEM where
  typeOf _ = mkTyConApp tc_M_SIG_ITEM []
instance Typeable M_BASIC_ITEM where
  typeOf _ = mkTyConApp tc_M_BASIC_ITEM []
instance Typeable ModalSign where
  typeOf _ = mkTyConApp modalSignTc []

instance Category Modal MSign ModalMor  
    where
         -- ide :: id -> object -> morphism
         ide Modal = idMor dummy
         -- comp :: id -> morphism -> morphism -> Maybe morphism
         comp Modal = compose (const id)
         -- dom, cod :: id -> morphism -> object
         dom Modal = msource
         cod Modal = mtarget
         -- legal_obj :: id -> object -> Bool
         legal_obj Modal = legalSign
         -- legal_mor :: id -> morphism -> Bool
         legal_mor Modal = legalMor

-- abstract syntax, parsing (and printing)

instance Syntax Modal M_BASIC_SPEC
                SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec Modal = Just $ basicSpec modal_reserved_words
         parse_symb_items Modal = Just $ symbItems modal_reserved_words
         parse_symb_map_items Modal = Just $ symbMapItems modal_reserved_words

-- Modal logic

instance Sentences Modal ModalFORMULA () MSign ModalMor Symbol where
      map_sen Modal = mapSen map_M_FORMULA
      parse_sentence Modal = Nothing
      sym_of Modal = symOf
      symmap_of Modal = morphismToSymbMap
      sym_name Modal = symName
      provers Modal = [] 
      cons_checkers Modal = []
      simplify_sen Modal = simplifySen minExpForm rmTypesMod rmTypesMod

-- reTypesMod
rmTypesMod :: Sign M_FORMULA ModalSign -> M_FORMULA -> M_FORMULA
rmTypesMod sign mFormula =
    case mFormula of
      Box mod form pos -> 
	  let mod' = case mod of
	             Term_mod term -> Term_mod $ rmTypesT minExpForm rmTypesMod sign term
		     t -> t
	  in Box mod' (simplifySen minExpForm rmTypesMod rmTypesMod sign form) pos
      Diamond mod form pos ->
	  let mod' = case mod of
	             Term_mod term -> Term_mod $ rmTypesT minExpForm rmTypesMod sign term
		     t -> t
	  in Diamond mod' (simplifySen minExpForm rmTypesMod rmTypesMod sign form) pos


-- dummy	
simModal :: Sign M_FORMULA ModalSign -> M_FORMULA -> M_FORMULA
simModal sign mFormula =
    case mFormula of
      Box mod form pos -> 
	  let mod' = case mod of
		        Term_mod term -> Term_mod $ rmTypesT minExpForm simModal sign term
			t -> t
	  in Box mod' (simplifySen minExpForm simModal simModal sign form) pos
      Diamond mod form pos ->
	  let mod' = case mod of
	             Term_mod term -> Term_mod $ rmTypesT minExpForm simModal sign term
		     t -> t
	  in Diamond mod' (simplifySen minExpForm simModal simModal sign form) pos


instance StaticAnalysis Modal M_BASIC_SPEC ModalFORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               MSign 
               ModalMor 
               Symbol RawSymbol where
         basic_analysis Modal = Just $ basicAnalysis resolveM_FORMULA 
                                noExtMixfixM minExpForm
                                ana_M_BASIC_ITEM ana_M_SIG_ITEM diffModalSign
         stat_symb_map_items Modal = statSymbMapItems
         stat_symb_items Modal = statSymbItems
         ensures_amalgamability Modal _ = 
             fail "Modal: ensures_amalgamability nyi" -- ???

         sign_to_basic_spec Modal _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw Modal = symbolToRaw
         id_to_raw Modal = idToRaw
         matches Modal = CASL.Morphism.matches
         
         empty_signature Modal = emptySign emptyModalSign
         signature_union Modal sigma1 sigma2 = 
           return $ addSig addModalSign sigma1 sigma2
         morphism_union Modal = morphismUnion (const id) addModalSign
         final_union Modal = finalUnion addModalSign
         is_subsig Modal = isSubSig isSubModalSign
         inclusion Modal = sigInclusion dummy isSubModalSign
         cogenerated_sign Modal = cogeneratedSign dummy
         generated_sign Modal = generatedSign dummy
         induced_from_morphism Modal = inducedFromMorphism dummy
         induced_from_to_morphism Modal = 
             inducedFromToMorphism dummy isSubModalSign

instance Logic Modal ()
               M_BASIC_SPEC ModalFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               MSign 
               ModalMor
               Symbol RawSymbol () where
         min_sublogic_basic_spec Modal _basic_spec = ()
         min_sublogic_sentence Modal _sentence = ()
         min_sublogic_symb_items Modal _symb_items = ()
         min_sublogic_symb_map_items Modal _symb_map_items = ()
         min_sublogic_sign Modal _sign = ()
         min_sublogic_morphism Modal _morphism = ()
         min_sublogic_symbol Modal _symbol = ()
--         sublogic_names Modal _ = ["Modal"]
--         all_sublogics Modal = [()]


