{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

   Instance of class Logic for CoCASL.
-}

{- todo:
-}

module CoCASL.Logic_CoCASL where

import CoCASL.AS_CoCASL
import CoCASL.CoCASLSign
import CoCASL.ATC_CoCASL
import CoCASL.Parse_AS
import CoCASL.StatAna
import CoCASL.LaTeX_CoCASL
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

data CoCASL = CoCASL deriving Show

instance Language CoCASL  where
 description _ = 
  "CoCASL is the coalgebraic extension of CASL."

type CoCASLMor = Morphism C_FORMULA CoCASLSign ()
type CoCASLFORMULA = FORMULA C_FORMULA

tc_C_FORMULA, tc_C_SIG_ITEM, tc_C_BASIC_ITEM, modalSignTc :: TyCon
tc_C_FORMULA     = mkTyCon "CoCASL.AS_CoCASL.C_FORMULA"
tc_C_SIG_ITEM    = mkTyCon "CoCASL.AS_CoCASL.C_SIG_ITEM"
tc_C_BASIC_ITEM  = mkTyCon "CoCASL.AS_CoCASL.C_BASIC_ITEM"
modalSignTc      = mkTyCon "CoCASL.CoCASLSign.CoCASLSign"

instance Typeable C_FORMULA where
  typeOf _ = mkTyConApp tc_C_FORMULA []
instance Typeable C_SIG_ITEM where
  typeOf _ = mkTyConApp tc_C_SIG_ITEM []
instance Typeable C_BASIC_ITEM where
  typeOf _ = mkTyConApp tc_C_BASIC_ITEM []
instance Typeable CoCASLSign where
  typeOf _ = mkTyConApp modalSignTc []

instance Category CoCASL CSign CoCASLMor  
    where
         -- ide :: id -> object -> morphism
         ide CoCASL = idMor dummy
         -- comp :: id -> morphism -> morphism -> Maybe morphism
         comp CoCASL = compose (const id)
         -- dom, cod :: id -> morphism -> object
         dom CoCASL = msource
         cod CoCASL = mtarget
         -- legal_obj :: id -> object -> Bool
         legal_obj CoCASL = legalSign
         -- legal_mor :: id -> morphism -> Bool
         legal_mor CoCASL = legalMor

-- abstract syntax, parsing (and printing)

instance Syntax CoCASL C_BASIC_SPEC
                SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec CoCASL = Just $ basicSpec cocasl_reserved_words
         parse_symb_items CoCASL = Just $ symbItems cocasl_reserved_words
         parse_symb_map_items CoCASL = Just $ symbMapItems cocasl_reserved_words

-- CoCASL logic

instance Sentences CoCASL CoCASLFORMULA () CSign CoCASLMor Symbol where
      map_sen CoCASL = mapSen map_C_FORMULA
      parse_sentence CoCASL = Nothing
      sym_of CoCASL = symOf
      symmap_of CoCASL = morphismToSymbMap
      sym_name CoCASL = symName
      provers CoCASL = [] 
      cons_checkers CoCASL = []

instance StaticAnalysis CoCASL C_BASIC_SPEC CoCASLFORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               CSign 
               CoCASLMor 
               Symbol RawSymbol where
         basic_analysis CoCASL = Just $ basicAnalysis minExpForm
                               ana_C_BASIC_ITEM ana_C_SIG_ITEM diffCoCASLSign
         stat_symb_map_items CoCASL = statSymbMapItems
         stat_symb_items CoCASL = statSymbItems
         ensures_amalgamability CoCASL _ = 
             fail "CoCASL: ensures_amalgamability nyi" -- ???

         sign_to_basic_spec CoCASL _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw CoCASL = symbolToRaw
         id_to_raw CoCASL = idToRaw
         matches CoCASL = CASL.Morphism.matches
         
         empty_signature CoCASL = emptySign emptyCoCASLSign
         signature_union CoCASL sigma1 sigma2 = 
           return $ addSig addCoCASLSign sigma1 sigma2
         morphism_union CoCASL = morphismUnion (const id) addCoCASLSign
         final_union CoCASL = finalUnion addCoCASLSign
         is_subsig CoCASL = isSubSig isSubCoCASLSign
         inclusion CoCASL = sigInclusion dummy isSubCoCASLSign
         cogenerated_sign CoCASL = cogeneratedSign dummy
         generated_sign CoCASL = generatedSign dummy
         induced_from_morphism CoCASL = inducedFromMorphism dummy
         induced_from_to_morphism CoCASL = 
             inducedFromToMorphism dummy isSubCoCASLSign

instance Logic CoCASL ()
               C_BASIC_SPEC CoCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign 
               CoCASLMor
               Symbol RawSymbol () where
         min_sublogic_basic_spec CoCASL _basic_spec = ()
         min_sublogic_sentence CoCASL _sentence = ()
         min_sublogic_symb_items CoCASL _symb_items = ()
         min_sublogic_symb_map_items CoCASL _symb_map_items = ()
         min_sublogic_sign CoCASL _sign = ()
         min_sublogic_morphism CoCASL _morphism = ()
         min_sublogic_symbol CoCASL _symbol = ()
--         sublogic_names CoCASL _ = ["CoCASL"]
--         all_sublogics CoCASL = [()]


