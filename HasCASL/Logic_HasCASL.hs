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

module HasCASL.Logic_HasCASL(HasCASL(HasCASL), HasCASL_Sublogics) where

import HasCASL.As
import HasCASL.Le
import HasCASL.AsToLe
import HasCASL.RawSym
import HasCASL.SymbItem
import HasCASL.Symbol
import HasCASL.ParseItem
import HasCASL.Morphism
import HasCASL.ATC_HasCASL()
import HasCASL.LaTeX_HasCASL()
import HasCASL.SymbolMapAnalysis
import HasCASL.Sublogic
import HasCASL.SimplifyTerm
import HasCASL.Merge
import Logic.Logic
import Data.Dynamic
import Common.DynamicUtils 

data HasCASL = HasCASL deriving (Show)
instance Language HasCASL where
 description _ = 
  "HasCASL - Algebraic Specification + Functional Programming = \ 
  \Environment for Formal Software Development\n\ 
  \This logic is based on the partial lambda calculus,\n\ 
  \and features subsorting, overloading and type class polymorphism\n\ 
  \See the HasCASL summary and further papers,\n\ 
  \available at http://www.tzi.de/cofi/HasCASL"

basicSpecTc, envTc, senTc, symbolTc, rawSymbolTc, 
    symbItemsTc, symbMapItemsTc, morphismTc, sublogicTc :: TyCon

basicSpecTc      = mkTyCon "HasCASL.As.BasicSpec"
envTc            = mkTyCon "HasCASL.Le.Env"
senTc            = mkTyCon "HasCASL.Le.Sentence"
symbolTc         = mkTyCon "HasCASL.Morphism.Symbol"
rawSymbolTc      = mkTyCon "HasCASL.Morphism.RawSymbol"
symbItemsTc      = mkTyCon "HasCASL.Symbol.SymbolItems"
symbMapItemsTc   = mkTyCon "HasCASL.Symbol.SymbolMapItems"
morphismTc       = mkTyCon "HasCASL.Morphism.Morphism"
sublogicTc       = mkTyCon "HasCASL.Sublogic.HasCASL_Sublogics"

instance Typeable BasicSpec where
    typeOf _ = mkTyConApp basicSpecTc []
instance Typeable Env where
    typeOf _ = mkTyConApp envTc []
instance Typeable Sentence where
    typeOf _ = mkTyConApp senTc []
instance Typeable Symbol where
    typeOf _ = mkTyConApp symbolTc []
instance Typeable RawSymbol where
    typeOf _ = mkTyConApp rawSymbolTc []
instance Typeable SymbItems where
    typeOf _ = mkTyConApp symbItemsTc []
instance Typeable SymbMapItems where
    typeOf _ = mkTyConApp symbMapItemsTc []
instance Typeable Morphism where
    typeOf _ = mkTyConApp morphismTc []
instance Typeable HasCASL_Sublogics where
    typeOf _ = mkTyConApp sublogicTc []

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

instance LatticeWithTop HasCASL_Sublogics where
    meet = HasCASL.Sublogic.sublogics_min
    join = HasCASL.Sublogic.sublogics_max
    top = HasCASL.Sublogic.top

instance Logic HasCASL HasCASL_Sublogics
               BasicSpec Sentence SymbItems SymbMapItems
               Env 
               Morphism
               Symbol RawSymbol () where
         stability _ = Testing

         sublogic_names HasCASL = HasCASL.Sublogic.sublogics_name
         all_sublogics HasCASL = HasCASL.Sublogic.sublogics_all

         data_logic HasCASL = Nothing

         is_in_basic_spec HasCASL = HasCASL.Sublogic.in_basicSpec
         is_in_sentence HasCASL = HasCASL.Sublogic.in_sentence
         is_in_symb_items HasCASL = HasCASL.Sublogic.in_symbItems
         is_in_symb_map_items HasCASL = HasCASL.Sublogic.in_symbMapItems
         is_in_sign HasCASL = HasCASL.Sublogic.in_env
         is_in_morphism HasCASL = HasCASL.Sublogic.in_morphism
         is_in_symbol HasCASL = HasCASL.Sublogic.in_symbol

         min_sublogic_basic_spec HasCASL = HasCASL.Sublogic.sl_basicSpec
         min_sublogic_sentence HasCASL = HasCASL.Sublogic.sl_sentence
         min_sublogic_symb_items HasCASL = HasCASL.Sublogic.sl_symbItems
         min_sublogic_symb_map_items HasCASL = HasCASL.Sublogic.sl_symbMapItems
         min_sublogic_sign HasCASL = HasCASL.Sublogic.sl_env
         min_sublogic_morphism HasCASL = HasCASL.Sublogic.sl_morphism
         min_sublogic_symbol HasCASL = HasCASL.Sublogic.sl_symbol
