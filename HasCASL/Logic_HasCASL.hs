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
import CASL.Print_AS_Basic()
import CASL.SymbolParser
import HasCASL.ParseItem
import Common.Result
import Logic.ParsecInterface
import Logic.Logic
import Common.AnnoState(emptyAnnos)
import Data.Dynamic
import Common.Lib.State
import qualified HasCASL.Morphism as M
import CASL.Morphism
import Common.PrettyPrint

type Sign = Env
type HasCASL_Sublogics = ()
type Sentence = Formula

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data HasCASL = HasCASL deriving (Show)
instance Language HasCASL -- default definition is okay

-- abstract syntax, parsing (and printing)

basicSpecTc :: TyCon
basicSpecTc = mkTyCon "HasCASL.As.BasicSpec"
envTc :: TyCon
envTc = mkTyCon "HasCASL.Le.Env"
formulaTc :: TyCon
formulaTc = mkTyCon "HasCASL.As.Formula"

instance Typeable BasicSpec where
    typeOf _ = mkAppTy basicSpecTc []

instance Typeable Env where
    typeOf _ = mkAppTy envTc []

instance Typeable Formula where
    typeOf _ = mkAppTy formulaTc []

instance Syntax HasCASL BasicSpec
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec HasCASL = Just(toParseFun basicSpec emptyAnnos)
	 parse_symb_items HasCASL = Just(toParseFun symbItems ())
	 parse_symb_map_items HasCASL = Just(toParseFun symbMapItems ())

instance Category HasCASL Env M.Morphism where 
    ide HasCASL e = M.ideMor e
    comp HasCASL m1 m2 = Just $ M.compMor m1 m2
    dom HasCASL m = M.msource m
    cod HasCASL m = M.mtarget m
    legal_obj HasCASL e = M.legalEnv e
    legal_mor HasCASL m = M.legalMor m

instance PrettyPrint Sign

instance Sentences HasCASL Sentence () Sign M.Morphism Symbol

instance StaticAnalysis HasCASL BasicSpec Sentence ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               M.Morphism 
               Symbol RawSymbol where
    basic_analysis HasCASL = Just ( \ (b, e, ga) ->
		let ne = snd $ (runState (anaBasicSpec ga b)) e 
		    in return (b, ne, initialEnv, [])) 
  
    signature_union HasCASL = merge
    empty_signature HasCASL = initialEnv
    induced_from_to_morphism HasCASL _ e1 e2 = return $ M.mkMorphism e1 e2
    induced_from_morphism HasCASL _ e = return $ M.ideMor e
    morphism_union HasCASL m1 m2 = M.morphismUnion m1 m2

    cogenerated_sign HasCASL _ e = return $ M.ideMor e

    stat_symb_map_items HasCASL = statSymbMapItems
    stat_symb_items HasCASL = statSymbItems
    symbol_to_raw HasCASL = symbolToRaw
    id_to_raw HasCASL = idToRaw
    matches HasCASL = CASL.Morphism.matches
    sym_name HasCASL = symName

instance Logic HasCASL HasCASL_Sublogics
               BasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               M.Morphism
               Symbol RawSymbol () 

