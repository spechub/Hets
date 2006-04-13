{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Here is the place where the class Logic is instantiated for HasCASL.
   Also the instances for Syntax and Category.

-}

module HasCASL.Logic_HasCASL(HasCASL(HasCASL)) where

import HasCASL.As
import HasCASL.Le
import HasCASL.AsToLe
import HasCASL.RawSym
import HasCASL.SymbItem
import HasCASL.Symbol
import HasCASL.ParseItem
import HasCASL.Morphism
import HasCASL.ATC_HasCASL()
import HasCASL.SymbolMapAnalysis
import HasCASL.Sublogic
import HasCASL.SimplifyTerm
import HasCASL.Merge
import Logic.Logic

data HasCASL = HasCASL deriving (Show)
instance Language HasCASL where
 description _ =
  "HasCASL - Algebraic Specification + Functional Programming = \
  \Environment for Formal Software Development\n\
  \This logic is based on the partial lambda calculus,\n\
  \and features subsorting, overloading and type class polymorphism\n\
  \See the HasCASL summary and further papers,\n\
  \available at http://www.tzi.de/cofi/HasCASL"

instance Syntax HasCASL BasicSpec
                SymbItems SymbMapItems
      where
         parse_basic_spec HasCASL = Just basicSpec
         parse_symb_items HasCASL = Just symbItems
         parse_symb_map_items HasCASL = Just symbMapItems

instance Category HasCASL Env Morphism where
    ide HasCASL e = ideMor e
    comp HasCASL m1 m2 = compMor m1 m2
    dom HasCASL m = msource m
    cod HasCASL m = mtarget m
    legal_obj HasCASL e = legalEnv e
    legal_mor HasCASL m = legalMor m

instance Sentences HasCASL Sentence () Env Morphism Symbol where
    map_sen HasCASL = mapSentence
    simplify_sen HasCASL = simplifySentence
    sym_name HasCASL = symName
    sym_of HasCASL = symOf
    symmap_of HasCASL = morphismToSymbMap
    parse_sentence HasCASL = Nothing
    provers HasCASL = []
    cons_checkers HasCASL = []

instance StaticAnalysis HasCASL BasicSpec Sentence ()
               SymbItems SymbMapItems
               Env
               Morphism
               Symbol RawSymbol where
    basic_analysis HasCASL = Just basicAnalysis
    signature_union HasCASL = merge
    empty_signature HasCASL = initialEnv
    induced_from_to_morphism HasCASL = inducedFromToMorphism
    induced_from_morphism HasCASL = inducedFromMorphism
    morphism_union HasCASL m1 m2 = morphismUnion m1 m2
    is_subsig HasCASL = isSubEnv
    inclusion HasCASL = inclusionMor

    cogenerated_sign HasCASL = cogeneratedSign
    generated_sign HasCASL = generatedSign

    sign_to_basic_spec HasCASL _ _ = error "sign_to_basic_spec: HasCASL"
    stat_symb_map_items HasCASL = statSymbMapItems
    stat_symb_items HasCASL = statSymbItems
    symbol_to_raw HasCASL = symbolToRaw
    id_to_raw HasCASL = idToRaw
    matches HasCASL = matchSymb

    final_union HasCASL = merge

instance LatticeWithTop Sublogic where
    meet = sublogic_min
    join = sublogic_max
    top = topLogic

instance Logic HasCASL Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env
               Morphism
               Symbol RawSymbol () where
         stability _ = Testing

         sublogic_names HasCASL = sublogic_name
         all_sublogics HasCASL = sublogics_all

         data_logic HasCASL = Nothing

         is_in_basic_spec HasCASL = in_basicSpec
         is_in_sentence HasCASL = in_sentence
         is_in_symb_items HasCASL = in_symbItems
         is_in_symb_map_items HasCASL = in_symbMapItems
         is_in_sign HasCASL = in_env
         is_in_morphism HasCASL = in_morphism
         is_in_symbol HasCASL = in_symbol

         min_sublogic_basic_spec HasCASL = sl_basicSpec
         min_sublogic_sentence HasCASL = sl_sentence
         min_sublogic_symb_items HasCASL = sl_symbItems
         min_sublogic_symb_map_items HasCASL = sl_symbMapItems
         min_sublogic_sign HasCASL = sl_env
         min_sublogic_morphism HasCASL = sl_morphism
         min_sublogic_symbol HasCASL = sl_symbol
