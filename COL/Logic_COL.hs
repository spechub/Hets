{- |
Module      :  $Header$
Description :  COL instance of class Logic
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic)

COL instance of class Logic
-}

module COL.Logic_COL where

import COL.AS_COL
import COL.COLSign
import COL.ATC_COL()
import COL.Parse_AS()
import COL.StatAna
import COL.Print_AS()
import CASL.Sign
import CASL.StaticAna
import CASL.MixfixParser
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.MapSentence
import CASL.SymbolParser
import Logic.Logic

data COL = COL deriving Show

instance Language COL where
 description _ =
  "COLCASL extends CASL by constructors and observers"

type C_BASIC_SPEC = BASIC_SPEC () COL_SIG_ITEM ()
type CSign = Sign () COLSign
type COLMor = Morphism () COLSign ()
type COLFORMULA = FORMULA ()

instance Category COL CSign COLMor
    where
         -- ide :: id -> object -> morphism
         ide COL = idMor ()
         -- comp :: id -> morphism -> morphism -> Maybe morphism
         comp COL = compose (const id)
         -- dom, cod :: id -> morphism -> object
         dom COL = msource
         cod COL = mtarget
         -- legal_obj :: id -> object -> Bool
         legal_obj COL = legalSign
         -- legal_mor :: id -> morphism -> Bool
         legal_mor COL = legalMor

-- abstract syntax, parsing (and printing)

instance Syntax COL C_BASIC_SPEC
                SYMB_ITEMS SYMB_MAP_ITEMS
      where
         parse_basic_spec COL = Just $ basicSpec col_reserved_words
         parse_symb_items COL = Just $ symbItems col_reserved_words
         parse_symb_map_items COL = Just $ symbMapItems col_reserved_words

-- COL logic

instance Sentences COL COLFORMULA CSign COLMor Symbol where
      map_sen COL m = return . mapSen (\ _ -> id) m
      parse_sentence COL = Nothing
      sym_of COL = symOf
      symmap_of COL = morphismToSymbMap
      sym_name COL = symName

instance StaticAnalysis COL C_BASIC_SPEC COLFORMULA
               SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               COLMor
               Symbol RawSymbol where
         basic_analysis COL = Just $ basicAnalysis (const return)
                              (const return) ana_COL_SIG_ITEM
                              emptyMix
         stat_symb_map_items COL = statSymbMapItems
         stat_symb_items COL = statSymbItems
         ensures_amalgamability COL _ =
             fail "COL: ensures_amalgamability nyi" -- ???

         sign_to_basic_spec COL _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw COL = symbolToRaw
         id_to_raw COL = idToRaw
         matches COL = CASL.Morphism.matches

         empty_signature COL = emptySign emptyCOLSign
         signature_union COL sigma1 sigma2 =
           return $ addSig addCOLSign sigma1 sigma2
         morphism_union COL = morphismUnion (const id) addCOLSign
         final_union COL = finalUnion addCOLSign
         is_subsig COL = isSubSig isSubCOLSign
         inclusion COL = sigInclusion () isSubCOLSign
         cogenerated_sign COL = cogeneratedSign ()
         generated_sign COL = generatedSign ()
         induced_from_morphism COL = inducedFromMorphism ()
         induced_from_to_morphism COL =
             inducedFromToMorphism () isSubCOLSign diffCOLSign

instance Logic COL ()
               C_BASIC_SPEC COLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CSign
               COLMor
               Symbol RawSymbol () where
         empty_proof_tree _ = ()
