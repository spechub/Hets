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
import HasCASL.Builtin
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
import Common.Doc
import Common.DocUtils

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
    print_named _ = printAnnoted ( \ s -> case s of
        Formula t -> addBullet . changeGlobalAnnos addBuiltins $ pretty t
        DatatypeSen _ -> pretty s
        ProgEqSen _ _ _ -> changeGlobalAnnos addBuiltins $ pretty s)
        . fromLabelledSen                                                 
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
    signature_difference HasCASL s = return . diffEnv s
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

instance SemiLatticeWithTop Sublogic where
    join = sublogic_max
    top = topLogic

instance Sublogics Sublogic where
    sublogic_names = sublogic_name

instance MinSublogic Sublogic BasicSpec where
    minSublogic = sl_basicSpec

instance MinSublogic Sublogic Sentence where
    minSublogic = sl_sentence

instance MinSublogic Sublogic SymbItems where
    minSublogic = sl_symbItems

instance MinSublogic Sublogic SymbMapItems where
    minSublogic = sl_symbMapItems

instance MinSublogic Sublogic Env where
    minSublogic = sl_env

instance MinSublogic Sublogic Morphism where
    minSublogic = sl_morphism

instance MinSublogic Sublogic Symbol where
    minSublogic = sl_symbol

instance ProjectSublogic Sublogic BasicSpec
instance ProjectSublogicM Sublogic SymbItems
instance ProjectSublogicM Sublogic SymbMapItems
instance ProjectSublogic Sublogic Env
instance ProjectSublogic Sublogic Morphism
instance ProjectSublogicM Sublogic Symbol

instance Logic HasCASL Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env
               Morphism
               Symbol RawSymbol () where
         stability _ = Testing
         all_sublogics _ = sublogics_all
