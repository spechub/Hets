-- {-# OPTIONS -fno-warn-missing-methods #-}
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

   Here is the place where the class Logic is instantiated for HasCASL.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions
-}

module HasCASL.Logic_HasCASL(HasCASL(HasCASL), HasCASL_Sublogics) where

import HasCASL.As
import HasCASL.Le
import HasCASL.PrintLe
import HasCASL.AsToLe
import HasCASL.Symbol
import HasCASL.ParseItem
import HasCASL.TypeCheck
import Common.Result
import Logic.ParsecInterface
import Logic.Logic
import Common.AnnoState(emptyAnnos)
import Data.Dynamic
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Lib.State
import HasCASL.Morphism
import Common.PrettyPrint
import HasCASL.ATC_HasCASL
import HasCASL.LaTeX_HasCASL
import HasCASL.SymbolMapAnalysis

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
         parse_basic_spec HasCASL = Just(toParseFun basicSpec emptyAnnos)
	 parse_symb_items HasCASL = Just(toParseFun symbItems emptyAnnos)
	 parse_symb_map_items HasCASL = Just(toParseFun symbMapItems 
					     emptyAnnos)

instance Category HasCASL Env Morphism where 
    ide HasCASL e = ideMor e
    comp HasCASL m1 m2 = compMor m1 m2
    dom HasCASL m = msource m
    cod HasCASL m = mtarget m
    legal_obj HasCASL e = legalEnv e
    legal_mor HasCASL m = legalMor m

instance Sentences HasCASL Term () Env Morphism Symbol where
    sym_name HasCASL = symName
    sym_of HasCASL = symOf -- \ _ -> Set.empty
    symmap_of HasCASL = morphismToSymbMap

instance StaticAnalysis HasCASL BasicSpec Term ()
               SymbItems SymbMapItems
               Env 
               Morphism 
               Symbol RawSymbol where
    basic_analysis HasCASL = Just basicAnalysis 
    signature_union HasCASL = mergeEnv
    empty_signature HasCASL = initialEnv
    induced_from_to_morphism HasCASL = inducedFromToMorphism
    induced_from_morphism HasCASL = inducedFromMorphism
    morphism_union HasCASL m1 m2 = morphismUnion m1 m2
    inclusion HasCASL = inclusionMor

    cogenerated_sign HasCASL = cogeneratedSign
    generated_sign HasCASL = generatedSign

    stat_symb_map_items HasCASL = statSymbMapItems
    stat_symb_items HasCASL = statSymbItems
    symbol_to_raw HasCASL = symbolToRaw
    id_to_raw HasCASL = idToRaw
    matches HasCASL = matchSymb

    final_union HasCASL = mergeEnv

instance Logic HasCASL HasCASL_Sublogics
               BasicSpec Term SymbItems SymbMapItems
               Env 
               Morphism
               Symbol RawSymbol () 

