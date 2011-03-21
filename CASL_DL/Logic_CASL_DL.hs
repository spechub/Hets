{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for CASL DL
Copyright   :  (c) Klaus Luettich, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Instance of class Logic for CASL DL
-}

module CASL_DL.Logic_CASL_DL (CASL_DL (..), DLMor, DLFORMULA) where

import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Result
import Common.ProofTree

import CASL_DL.AS_CASL_DL
import CASL_DL.Sign
import CASL_DL.PredefinedSign
import CASL_DL.ATC_CASL_DL ()
import CASL_DL.Parse_AS ()
import CASL_DL.StatAna

import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.MapSentence
import CASL.SymbolParser
import CASL.Taxonomy
import CASL.SimplifySen
import CASL.Logic_CASL ()
import CASL_DL.Sublogics

import Logic.Logic

data CASL_DL = CASL_DL deriving Show

instance Language CASL_DL where
 description _ = unlines
  [ "CASL_DL is at the same time an extension and a restriction of CASL."
  , "It additionally provides cardinality restrictions in a description logic"
  , "sense; and it limits the expressivity of CASL to the description logic"
  , "SHOIN(D). Hence it provides the following sublogics:"
  , "  * Card -- CASL plus cardinality restrictions on binary relations"
  , "  * DL   -- SHOIN(D)"
  , "  * SHIQ"
  , "  * SHOIQ" ]

type DLMor = Morphism DL_FORMULA CASL_DLSign (DefMorExt CASL_DLSign)
type DLFORMULA = FORMULA DL_FORMULA

instance SignExtension CASL_DLSign where
  isSubSignExtension = isSubCASL_DLSign

instance Syntax CASL_DL DL_BASIC_SPEC
                SYMB_ITEMS SYMB_MAP_ITEMS
      where
         parse_basic_spec CASL_DL = Just $ basicSpec casl_DL_reserved_words
         parse_symb_items CASL_DL = Just $ symbItems casl_DL_reserved_words
         parse_symb_map_items CASL_DL =
             Just $ symbMapItems casl_DL_reserved_words

-- CASL_DL logic

map_DL_FORMULA :: MapSen DL_FORMULA CASL_DLSign (DefMorExt CASL_DLSign)
map_DL_FORMULA mor (Cardinality ct pn varT natT qualT r) =
    Cardinality ct pn' varT' natT' qualT r
    where pn' = mapPrSymb mor pn
          varT' = mapTrm varT
          natT' = mapTrm natT
          mapTrm = mapTerm map_DL_FORMULA mor

instance Sentences CASL_DL DLFORMULA DLSign DLMor Symbol where
      map_sen CASL_DL m = return . mapSen map_DL_FORMULA m
      sym_of CASL_DL = symOf
      symmap_of CASL_DL = morphismToSymbMap
      sym_name CASL_DL = symName
      simplify_sen CASL_DL = simplifySen minDLForm simplifyCD

simplifyCD :: DLSign -> DL_FORMULA -> DL_FORMULA
simplifyCD sign (Cardinality ct ps t1 t2 t3 r) = simpCard
    where simpCard = maybe (card ps)
                           (const $ card $ Pred_name pn)
                           (resultToMaybe $
                            minDLForm sign $ card $ Pred_name pn)
          simp = rmTypesT minDLForm simplifyCD sign
          card psy = Cardinality ct psy (simp t1) (simp t2) t3 r
          pn = case ps of
               Pred_name n -> n
               Qual_pred_name n _pType _ -> n

instance StaticAnalysis CASL_DL DL_BASIC_SPEC DLFORMULA
               SYMB_ITEMS SYMB_MAP_ITEMS
               DLSign
               DLMor
               Symbol RawSymbol where
         basic_analysis CASL_DL = Just basicCASL_DLAnalysis
         stat_symb_map_items CASL_DL _ sml =
             statSymbMapItems sml >>= checkSymbolMapDL
         stat_symb_items CASL_DL _ = statSymbItems

         symbol_to_raw CASL_DL = symbolToRaw
         id_to_raw CASL_DL = idToRaw
         matches CASL_DL = CASL.Morphism.matches

         empty_signature CASL_DL = emptySign emptyCASL_DLSign
         signature_union CASL_DL s = return . addSig addCASL_DLSign s
         morphism_union CASL_DL = plainMorphismUnion addCASL_DLSign
         final_union CASL_DL = finalUnion addCASL_DLSign
         is_subsig CASL_DL = isSubSig isSubCASL_DLSign
         subsig_inclusion CASL_DL = sigInclusion emptyMorExt
         cogenerated_sign CASL_DL = cogeneratedSign emptyMorExt
         generated_sign CASL_DL = generatedSign emptyMorExt
         induced_from_morphism CASL_DL = inducedFromMorphism emptyMorExt
         induced_from_to_morphism CASL_DL =
             inducedFromToMorphism emptyMorExt isSubCASL_DLSign diffCASL_DLSign
         theory_to_taxonomy CASL_DL tgk mo =
             convTaxo tgk mo . extendSortRelWithTopSort

-- | extend the sort relation with sort Thing for the taxonomy display
extendSortRelWithTopSort :: Sign f e -> Sign f e
extendSortRelWithTopSort sig = sig {sortRel = addThing $ sortRel sig}
    where addThing r = Rel.union r (Rel.fromSet
                                    $ Set.map (\ x -> (x, topSort))
                                    $ sortSet sig)

instance Logic CASL_DL CASL_DL_SL
               DL_BASIC_SPEC DLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               DLSign
               DLMor
               Symbol RawSymbol ProofTree where
         stability _ = Unstable
         top_sublogic _ = SROIQ
         all_sublogics _ = [SROIQ]

instance MinSublogic CASL_DL_SL DLFORMULA where
    minSublogic _ = SROIQ

instance ProjectSublogic CASL_DL_SL DLMor where
    projectSublogic _ = id

instance MinSublogic CASL_DL_SL DLMor where
    minSublogic _ = SROIQ

instance ProjectSublogic CASL_DL_SL DLSign where
    projectSublogic _ = id

instance MinSublogic CASL_DL_SL DLSign where
    minSublogic _ = SROIQ

instance ProjectSublogicM CASL_DL_SL SYMB_MAP_ITEMS where
    projectSublogicM _ = Just

instance ProjectSublogicM CASL_DL_SL SYMB_ITEMS where
    projectSublogicM _ = Just

instance MinSublogic CASL_DL_SL SYMB_MAP_ITEMS where
    minSublogic _ = SROIQ

instance MinSublogic CASL_DL_SL SYMB_ITEMS where
    minSublogic _ = SROIQ

instance ProjectSublogic CASL_DL_SL DL_BASIC_SPEC where
    projectSublogic _ = id

instance MinSublogic CASL_DL_SL DL_BASIC_SPEC where
    minSublogic _ = SROIQ

instance SublogicName CASL_DL_SL where
    sublogicName SROIQ = show SROIQ

instance SemiLatticeWithTop CASL_DL_SL where
    join _ _ = SROIQ
    top = SROIQ

instance ProjectSublogic CASL_DL_SL Symbol where
    projectSublogic _ = id

instance ProjectSublogicM CASL_DL_SL Symbol where
    projectSublogicM _ = Just

instance MinSublogic CASL_DL_SL Symbol where
    minSublogic _ = SROIQ
