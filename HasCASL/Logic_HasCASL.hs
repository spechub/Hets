-- {-# OPTIONS -fno-warn-missing-methods #-}
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

   Here is the place where the class Logic is instantiated for HasCASL.
   Also the instances for Syntax and Category.

   todo:
     - writing real functions
-}

module HasCASL.Logic_HasCASL(HasCASL(HasCASL), HasCASL_Sublogics) where

import HasCASL.As
import HasCASL.Le
import HasCASL.PrintLe
import HasCASL.AsToLe
import HasCASL.RawSym
import HasCASL.SymbItem
import HasCASL.Symbol
import HasCASL.ParseItem
import HasCASL.Morphism
import HasCASL.ATC_HasCASL
import HasCASL.LaTeX_HasCASL
import HasCASL.SymbolMapAnalysis
import HasCASL.MapTerm
import Logic.Logic
import Data.Dynamic
import Common.Result

type HasCASL_Sublogics = ()

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data HasCASL = HasCASL deriving (Show)
instance Language HasCASL -- default definition is okay

basicSpecTc, envTc, termTc, symbolTc, rawSymbolTc, 
    symbItemsTc, symbMapItemsTc, morphismTc :: TyCon

basicSpecTc      = mkTyCon "HasCASL.As.BasicSpec"
envTc            = mkTyCon "HasCASL.Le.Env"
termTc           = mkTyCon "HasCASL.As.Term"
symbolTc         = mkTyCon "HasCASL.Morphism.Symbol"
rawSymbolTc      = mkTyCon "HasCASL.Morphism.RawSymbol"
symbItemsTc      = mkTyCon "HasCASL.Symbol.SymbolItems"
symbMapItemsTc   = mkTyCon "HasCASL.Symbol.SymbolMapItems"
morphismTc       = mkTyCon "HasCASL.Morphism.Morphism"

instance Typeable BasicSpec where
    typeOf _ = mkAppTy basicSpecTc []
instance Typeable Env where
    typeOf _ = mkAppTy envTc []
instance Typeable Term where
    typeOf _ = mkAppTy termTc []
instance Typeable Symbol where
    typeOf _ = mkAppTy symbolTc []
instance Typeable RawSymbol where
    typeOf _ = mkAppTy rawSymbolTc []
instance Typeable SymbItems where
    typeOf _ = mkAppTy symbItemsTc []
instance Typeable SymbMapItems where
    typeOf _ = mkAppTy symbMapItemsTc []
instance Typeable Morphism where
    typeOf _ = mkAppTy morphismTc []

-- abstract syntax, parsing (and printing)

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

instance Sentences HasCASL Term () Env Morphism Symbol where
    map_sen HasCASL = mapSen
    sym_name HasCASL = symName
    sym_of HasCASL = symOf -- \ _ -> Set.empty
    symmap_of HasCASL = morphismToSymbMap
    parse_sentence HasCASL = Nothing
    provers HasCASL = [] 
    cons_checkers HasCASL = []

instance StaticAnalysis HasCASL BasicSpec Term ()
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

    stat_symb_map_items HasCASL = statSymbMapItems
    stat_symb_items HasCASL = statSymbItems
    symbol_to_raw HasCASL = symbolToRaw
    id_to_raw HasCASL = idToRaw
    matches HasCASL = matchSymb

    final_union HasCASL = merge

instance Logic HasCASL HasCASL_Sublogics
               BasicSpec Term SymbItems SymbMapItems
               Env 
               Morphism
               Symbol RawSymbol () where
         min_sublogic_basic_spec HasCASL _basic_spec = ()
         min_sublogic_sentence HasCASL _sentence = ()
         min_sublogic_symb_items HasCASL _symb_items = ()
         min_sublogic_symb_map_items HasCASL _symb_map_items = ()
         min_sublogic_sign HasCASL _sign = ()
         min_sublogic_morphism HasCASL _morphism = ()
         min_sublogic_symbol HasCASL _symbol = ()


