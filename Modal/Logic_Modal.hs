{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Instance of class Logic for modal logic.
-}

module Modal.Logic_Modal where

import Modal.AS_Modal
import Modal.ModalSign
import Common.AS_Annotation
import Common.AnnoState(emptyAnnos)
import Common.Lib.Parsec
import Logic.Logic

import CASL.Sign
import CASL.StaticAna
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.MapSentence
import Modal.ATC_Modal
import Modal.LaTeX_Modal
import Data.Dynamic

data Modal = Modal deriving Show

instance Language Modal  -- default definition is okay

type MSign = Sign M_FORMULA ModalSign
type ModalMor = Morphism M_FORMULA ModalSign ()
type ModalFORMULA = FORMULA M_FORMULA

tc_M_FORMULA, tc_M_SIG_ITEM, tc_M_BASIC_ITEM, modalSignTc :: TyCon

tc_M_FORMULA     = mkTyCon "Modal.AS_Modal.M_FORMULA"
tc_M_SIG_ITEM    = mkTyCon "Modal.AS_Modal.M_SIG_ITEM"
tc_M_BASIC_ITEM  = mkTyCon "Modal.AS_Modal.M_BASIC_ITEM"
modalSignTc      = mkTyCon "Modal.ModalSign.ModalSign"

instance Typeable M_FORMULA where
  typeOf _ = mkAppTy tc_M_FORMULA []
instance Typeable M_SIG_ITEM where
  typeOf _ = mkAppTy tc_M_SIG_ITEM []
instance Typeable M_BASIC_ITEM where
  typeOf _ = mkAppTy tc_M_BASIC_ITEM []
instance Typeable ModalSign where
  typeOf _ = mkAppTy modalSignTc []

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
         parse_basic_spec Modal = Nothing
	 parse_symb_items Modal = Nothing
	 parse_symb_map_items Modal = Nothing

-- Modal logic

instance Sentences Modal ModalFORMULA () MSign ModalMor Symbol where
      map_sen Modal = mapSen
      parse_sentence Modal = Nothing
      sym_of Modal = symOf
      symmap_of Modal = morphismToSymbMap
      sym_name Modal = symName
      provers Modal = [] 
      cons_checkers Modal = []

instance StaticAnalysis Modal M_BASIC_SPEC ModalFORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               MSign 
               ModalMor 
               Symbol RawSymbol where
         basic_analysis Modal = Just $ basicAnalysis 
			       (const id) (const id) return
         stat_symb_map_items Modal = statSymbMapItems
         stat_symb_items Modal = statSymbItems
	 ensures_amalgamability Modal _ = fail "ensures_amalgamability nyi" -- ???

         sign_to_basic_spec Modal _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw Modal = symbolToRaw
         id_to_raw Modal = idToRaw
         matches Modal = CASL.Morphism.matches
         
         empty_signature Modal = emptySign emptyModalSign
         signature_union Modal sigma1 sigma2 = 
           return $ addSig sigma1 sigma2
         morphism_union Modal = morphismUnion (const id)
	 final_union Modal = finalUnion
         is_subsig Modal = isSubSig
         inclusion Modal = sigInclusion dummy
         cogenerated_sign Modal = cogeneratedSign dummy
         generated_sign Modal = generatedSign dummy
         induced_from_morphism Modal = inducedFromMorphism dummy
         induced_from_to_morphism Modal = inducedFromToMorphism dummy

instance Logic Modal ()
               M_BASIC_SPEC ModalFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               MSign 
               ModalMor
               Symbol RawSymbol () where
         sublogic_names Modal _ = ["Modal"]
         all_sublogics Modal = [()]

         data_logic Modal = Nothing

