{-# OPTIONS -fno-warn-missing-methods #-}
{- HetCATS/HasCASL/Logic_HasCASL.hs
   $Id$
   Authors: C. Maeder
   Year:    2003

   Here is the place where the class Logic is instantiated for HasCASL.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions

-}

module HasCASL.Logic_HasCASL where

import HasCASL.As
import HasCASL.Le
import HasCASL.AsToLe
import CASL.AS_Basic_CASL(SYMB_ITEMS, SYMB_MAP_ITEMS)
import HasCASL.ParseItem
import HasCASL.Merge
import CASL.SymbolParser
import Logic.ParsecInterface
import Logic.Logic
import Common.AnnoState(emptyAnnos)
import Data.Dynamic
import Control.Monad.State
import HasCASL.Morphism
import qualified CASL.Sign
import qualified CASL.Static
import qualified CASL.Sublogics
import qualified CASL.Logic_CASL

type Sign = Env
type HasCASL_Sublogics = CASL.Sublogics.CASL_Sublogics
type Sentence = Formula
type Symbol = CASL.Sign.Symbol
type RawSymbol = CASL.Sign.RawSymbol

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data HasCASL = HasCASL deriving (Show)
instance Language HasCASL -- default definition is okay

-- abstract syntax, parsing (and printing)

basicSpecTc :: TyCon
basicSpecTc = mkTyCon "HasCASL.As.BasicSpec"
signTc :: TyCon
signTc = mkTyCon "HasCASL.Le.Env"
sentenceTc :: TyCon
sentenceTc = mkTyCon "HasCASL.As.Formula"

instance Typeable BasicSpec where
    typeOf _ = mkAppTy basicSpecTc []

instance Typeable Sign where
    typeOf _ = mkAppTy signTc []

instance Typeable Sentence where
    typeOf _ = mkAppTy sentenceTc []

instance Syntax HasCASL BasicSpec
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec HasCASL = Just(toParseFun basicSpec emptyAnnos)
	 parse_symb_items HasCASL = Just(toParseFun symbItems ())
	 parse_symb_map_items HasCASL = Just(toParseFun symbMapItems ())

instance Category HasCASL Env Morphism where 
    ide HasCASL e = ideMor e
    comp HasCASL m1 m2 = Just $ compMor m1 m2
    dom HasCASL m = msource m
    cod HasCASL m = mtarget m
    legal_obj HasCASL e = legalEnv e
    legal_mor HasCASL m = legalMor m

instance Sentences HasCASL Sentence () Sign Morphism Symbol

instance StaticAnalysis HasCASL BasicSpec Sentence ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol where
    basic_analysis HasCASL = Just ( \ (b, e, _) ->
		let ne = snd $ (runState (anaBasicSpec b)) e 
		    in return (ne, initialEnv, [])) 
    stat_symb_map_items HasCASL = CASL.Static.statSymbMapItems
    stat_symb_items HasCASL = CASL.Static.statSymbItems
    symbol_to_raw HasCASL = CASL.Static.symbolToRaw
    id_to_raw HasCASL = CASL.Static.idToRaw
    matches HasCASL = CASL.Static.matches
    sym_name HasCASL = CASL.Static.symName
  
    signature_union HasCASL = merge
    empty_signature HasCASL = initialEnv
    induced_from_to_morphism HasCASL _ e1 e2 = return $ mkMorphism e1 e2
    induced_from_morphism HasCASL _ e = return $ ideMor e
    morphism_union HasCASL m1 m2 = morphismUnion m1 m2

instance Logic HasCASL HasCASL_Sublogics
               BasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol () where
         sublogic_names HasCASL = CASL.Sublogics.sublogics_name
         all_sublogics HasCASL = CASL.Sublogics.sublogics_all
         is_in_symb_items HasCASL = CASL.Sublogics.in_symb_items
         is_in_symb_map_items HasCASL = CASL.Sublogics.in_symb_map_items
         is_in_symbol HasCASL = CASL.Sublogics.in_symbol

         min_sublogic_symb_items HasCASL = CASL.Sublogics.sl_symb_items
         min_sublogic_symb_map_items HasCASL = CASL.Sublogics.sl_symb_map_items
         min_sublogic_symbol HasCASL = CASL.Sublogics.sl_symbol

         proj_sublogic_symb_items HasCASL = CASL.Sublogics.pr_symb_items
         proj_sublogic_symb_map_items HasCASL = CASL.Sublogics.pr_symb_map_items
         proj_sublogic_symbol HasCASL = CASL.Sublogics.pr_symbol

