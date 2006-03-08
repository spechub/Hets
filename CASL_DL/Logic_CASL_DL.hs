{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

   Instance of class Logic for CASL DL.
-}

{- todo:
    - implement a symbol mapping that forbids mapping of predefined symbols 
       from emptySign
-}

module CASL_DL.Logic_CASL_DL where

import CASL_DL.AS_CASL_DL
import CASL_DL.Sign
import CASL_DL.PredefinedSign
import CASL_DL.ATC_CASL_DL ()
import CASL_DL.Parse_AS ()
import CASL_DL.StatAna
import CASL_DL.LaTeX_AS ()

import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.MapSentence
import CASL.SymbolParser
import CASL.Taxonomy
import CASL.SimplifySen

import Logic.Logic

data CASL_DL = CASL_DL deriving Show

instance Language CASL_DL  where
 description _ = 
  "CASL_DL is at the same time an extension and a restriction of CASL.\n\
  \It additionally provides cardinality restrictions in a description logic\n\
  \sense; and it limits the expressivity of CASL to the description logic\n\
  \SHOIN(D). Hence it provides the following sublogics: \n\
  \  * Card -- CASL plus cardinality restrictions on binary relations\n\
  \  * DL   -- SHOIN(D)\n\
  \  * SHIQ\n\
  \  * SHOIQ\n"

type DLMor = Morphism DL_FORMULA CASL_DLSign ()
type DLFORMULA = FORMULA DL_FORMULA

instance Category CASL_DL DLSign DLMor  
    where
         -- ide :: id -> object -> morphism
         ide CASL_DL = idMor dummy
         -- comp :: id -> morphism -> morphism -> Maybe morphism
         comp CASL_DL = compose (const id)
         -- dom, cod :: id -> morphism -> object
         dom CASL_DL = msource
         cod CASL_DL = mtarget
         -- legal_obj :: id -> object -> Bool
         legal_obj CASL_DL = legalSign
         -- legal_mor :: id -> morphism -> Bool
         legal_mor CASL_DL = legalMor

-- abstract syntax, parsing (and printing)

instance Syntax CASL_DL DL_BASIC_SPEC
                SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec CASL_DL = Just $ basicSpec casl_DL_reserved_words
         parse_symb_items CASL_DL = Just $ symbItems casl_DL_reserved_words
         parse_symb_map_items CASL_DL = 
             Just $ symbMapItems casl_DL_reserved_words

-- CASL_DL logic

map_DL_FORMULA :: MapSen DL_FORMULA CASL_DLSign ()
map_DL_FORMULA mor (Cardinality ct pn varT natT r) =
    Cardinality ct pn varT' natT' r
    where varT' = mapTrm varT
          natT' = mapTrm natT
          mapTrm = mapTerm map_DL_FORMULA mor

instance Sentences CASL_DL DLFORMULA () DLSign DLMor Symbol where
      map_sen CASL_DL m = return . mapSen map_DL_FORMULA m
      parse_sentence CASL_DL = Nothing
      sym_of CASL_DL = symOf
      symmap_of CASL_DL = morphismToSymbMap
      sym_name CASL_DL = symName
      provers CASL_DL = [] 
      cons_checkers CASL_DL = []
      simplify_sen CASL_DL = simplifySen minDLForm simplifyCD

simplifyCD :: DLSign -> DL_FORMULA -> DL_FORMULA
simplifyCD sign (Cardinality ct pn t1 t2 r) =
    Cardinality ct pn (simp t1) (simp t2) r
    where simp = rmTypesT minDLForm simplifyCD sign

instance StaticAnalysis CASL_DL DL_BASIC_SPEC DLFORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               DLSign 
               DLMor 
               Symbol RawSymbol where
         basic_analysis CASL_DL = Just $ basicCASL_DLAnalysis
         stat_symb_map_items CASL_DL = statSymbMapItems
         stat_symb_items CASL_DL = statSymbItems
         ensures_amalgamability CASL_DL _ = 
             fail "CASL_DL: ensures_amalgamability nyi" -- ???

         sign_to_basic_spec CASL_DL _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw CASL_DL = symbolToRaw
         id_to_raw CASL_DL = idToRaw
         matches CASL_DL = CASL.Morphism.matches
         
         empty_signature CASL_DL = dataSign
         signature_union CASL_DL sigma1 sigma2 = 
           return $ addSig addCASL_DLSign sigma1 sigma2
         morphism_union CASL_DL = morphismUnion (const id) addCASL_DLSign
         final_union CASL_DL = finalUnion addCASL_DLSign
         is_subsig CASL_DL = isSubSig isSubCASL_DLSign
         inclusion CASL_DL = sigInclusion dummy isSubCASL_DLSign
         cogenerated_sign CASL_DL = cogeneratedSign dummy
         generated_sign CASL_DL = generatedSign dummy
         induced_from_morphism CASL_DL = inducedFromMorphism dummy
         induced_from_to_morphism CASL_DL = 
             inducedFromToMorphism dummy isSubCASL_DLSign
         theory_to_taxonomy CASL_DL = convTaxo

instance Logic CASL_DL ()
               DL_BASIC_SPEC DLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               DLSign 
               DLMor
               Symbol RawSymbol () where
         stability _ = Unstable
         min_sublogic_basic_spec CASL_DL _basic_spec = ()
         min_sublogic_sentence CASL_DL _sentence = ()
         min_sublogic_symb_items CASL_DL _symb_items = ()
         min_sublogic_symb_map_items CASL_DL _symb_map_items = ()
         min_sublogic_sign CASL_DL _sign = ()
         min_sublogic_morphism CASL_DL _morphism = ()
         min_sublogic_symbol CASL_DL _symbol = ()
--         sublogic_names CASL_DL _ = ["CASL_DL"]
--         all_sublogics CASL_DL = [()]
