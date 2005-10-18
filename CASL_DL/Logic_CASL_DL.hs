{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Instance of class Logic for CASL DL.
-}

{- todo:

-}

module CASL_DL.Logic_CASL_DL where

import CASL_DL.AS_CASL_DL
import CASL_DL.Sign
import CASL_DL.ATC_CASL_DL
import CASL_DL.Parse_AS
-- import CASL_DL.StatAna
import CASL_DL.LaTeX_AS

import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.MapSentence
import CASL.SymbolParser
import CASL.Taxonomy

import Logic.Logic
import Data.Dynamic
import Common.DynamicUtils
 
import CASL.SimplifySen

data CASL_DL = CASL_DL deriving Show

instance Language CASL_DL  where
 description _ = 
  "CASL_DL is at the same time an extension and a restriction of CASL.\n\
  \It additionally provides cardinality restrictions in a description logic\n\
  \sense. It limits the expressivity of CASL to the description logic SHOIN(D)\n"

type CDSign = Sign DL_FORMULA CASL_DLSign
type CDMor = Morphism DL_FORMULA CASL_DLSign ()
type CDFORMULA = FORMULA DL_FORMULA

tc_CD_FORMULA, tc_CD_SIG_ITEM, tc_CD_BASIC_ITEM, cdSignTc :: TyCon
tc_CD_FORMULA     = mkTyCon "CASL_DL.AS_CASL_DL.DL_FORMULA"
tc_CD_SIG_ITEM    = mkTyCon "CASL_DL.AS_CASL_DL.DL_SIG_ITEM"
tc_CD_BASIC_ITEM  = mkTyCon "CASL_DL.AS_CASL_DL.DL_BASIC_ITEM"
cdSignTc      = mkTyCon "CASL_DL.Sign.CASL_DLSign"

instance Typeable DL_FORMULA where
  typeOf _ = mkTyConApp tc_CD_FORMULA []
-- instance Typeable M_SIG_ITEM where
--  typeOf _ = mkTyConApp tc_CD_SIG_ITEM []
-- instance Typeable M_BASIC_ITEM where
--  typeOf _ = mkTyConApp tc_CD_BASIC_ITEM []
instance Typeable CASL_DLSign where
  typeOf _ = mkTyConApp cdSignTc []

instance Category CASL_DL CDSign CDMor  
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

map_CD_FORMULA :: MapSen DL_FORMULA CASL_DLSign ()
map_CD_FORMULA mor = id
   -- (Cardinality ct pn varT natT r) = 

instance Sentences CASL_DL CDFORMULA () CDSign CDMor Symbol where
      map_sen CASL_DL m = return . mapSen map_CD_FORMULA m
      parse_sentence CASL_DL = Nothing
      sym_of CASL_DL = symOf
      symmap_of CASL_DL = morphismToSymbMap
      sym_name CASL_DL = symName
      provers CASL_DL = [] 
      cons_checkers CASL_DL = []
      simplify_sen CASL_DL _ = id -- simplifySen tCheckCASL_DL simpCASL_DL

{-
-- simplifySen for ExtFORMULA   
simCASL_DL :: Sign M_FORMULA ModalSign -> M_FORMULA -> M_FORMULA
simCASL_DL sign (BoxOrDiamond b md form pos) =
    let mod' = case md of
                        Term_mod term -> Term_mod $ rmTypesT minExpForm 
                                         simCASL_DL sign term
                        t -> t
    in BoxOrDiamond b mod' 
                 (simplifySen minExpForm simCASL_DL sign form) pos

rmTypesExt :: a -> b -> b
rmTypesExt _ f = f

-}
instance StaticAnalysis CASL_DL DL_BASIC_SPEC CDFORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               CDSign 
               CDMor 
               Symbol RawSymbol where
         basic_analysis CASL_DL = Nothing -- Just $ basicCASL_DLAnalysis
         stat_symb_map_items CASL_DL = statSymbMapItems
         stat_symb_items CASL_DL = statSymbItems
         ensures_amalgamability CASL_DL _ = 
             fail "CASL_DL: ensures_amalgamability nyi" -- ???

         sign_to_basic_spec CASL_DL _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw CASL_DL = symbolToRaw
         id_to_raw CASL_DL = idToRaw
         matches CASL_DL = CASL.Morphism.matches
         
         empty_signature CASL_DL = emptySign emptyCASL_DLSign
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
               DL_BASIC_SPEC CDFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CDSign 
               CDMor
               Symbol RawSymbol () where
         min_sublogic_basic_spec CASL_DL _basic_spec = ()
         min_sublogic_sentence CASL_DL _sentence = ()
         min_sublogic_symb_items CASL_DL _symb_items = ()
         min_sublogic_symb_map_items CASL_DL _symb_map_items = ()
         min_sublogic_sign CASL_DL _sign = ()
         min_sublogic_morphism CASL_DL _morphism = ()
         min_sublogic_symbol CASL_DL _symbol = ()
--         sublogic_names CASL_DL _ = ["CASL_DL"]
--         all_sublogics CASL_DL = [()]
