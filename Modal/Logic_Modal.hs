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
import Common.AS_Annotation
import Common.AnnoState(emptyAnnos)
import Common.Lib.Parsec
import Logic.Logic

import CASL.Sign
import CASL.StaticAna
import CASL.Morphism
import CASL.SymbolMapAnalysis
import Data.Dynamic

data Modal = Modal deriving Show

instance Language Modal  -- default definition is okay

type ModalSign = Sign M_FORMULA ModalSign
type ModalMor = Morphism M_FORMULA ModalSign ()

dummy :: a -> b -> ()
dummy _ _ = ()

-- Typeable instance
tc_BASIC_SPEC, tc_SYMB_ITEMS, tc_SYMB_MAP_ITEMS, casl_SublocigsTc,
	     sentenceTc, signTc, morphismTc, symbolTc, rawSymbolTc :: TyCon

tc_M_BASIC_SPEC     = mkTyCon "Modal.AS_Basic_Modal.Morphism.BASIC_SPEC"
sentenceTc       = mkTyCon "Modal.AS_Modal.ModalFORMULA"
signTc           = mkTyCon "Modal.Morphism.ModalSign"
morphismTc       = mkTyCon "Modal.Morphism.ModalMor"

instance Typeable M_BASIC_SPEC where
  typeOf _ = mkAppTy tc_M_BASIC_SPEC []
instance Typeable ModalFORMULA where
  typeOf _ = mkAppTy sentenceTc []
instance Typeable ModalSign where
  typeOf _ = mkAppTy signTc []
instance Typeable ModalMor where
  typeOf _ = mkAppTy morphismTc []

instance Category Modal ModalSign ModalMor  
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

instance Syntax Modal ModalBasicSpec
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec Modal = Nothing
	 parse_symb_items Modal = Nothing
	 parse_symb_map_items Modal = Nothing

-- Modal logic

instance Sentences Modal ModalFORMULA () ModalSign ModalMor Symbol where
      map_sen Modal = mapSen
      parse_sentence Modal = Nothing
      sym_of Modal = symOf
      symmap_of Modal = morphismToSymbMap
      sym_name Modal = symName
      provers Modal = [] 
      cons_checkers Modal = []

instance StaticAnalysis Modal ModalBasicSpec ModalFORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               ModalSign 
               ModalMor 
               Symbol RawSymbol where
         basic_analysis Modal = Just $ basicAnalysis 
			       (const id) (const id) return
         stat_symb_map_items Modal = statSymbMapItems
         stat_symb_items Modal = statSymbItems
	 ensures_amalgamability Modal _ = fail "ensures_amalgamability nyi" -- ???

         sign_to_basic_spec Modal _sigma _sens = M_Basic_spec [] -- ???

         symbol_to_raw Modal = symbolToRaw
         id_to_raw Modal = idToRaw
         matches Modal = Modal.Morphism.matches
         
         empty_signature Modal = emptySign ()
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

instance Logic Modal Modal.Sublogic.Modal_Sublogics
               ModalBasicSpec ModalFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               ModalSign 
               ModalMor
               Symbol RawSymbol () where
         sublogic_names Modal = ["Modal"]
         all_sublogics Modal = [()]

         data_logic Modal = Nothing

