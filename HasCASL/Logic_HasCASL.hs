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
import HasCASL.PrintAs
import CASL.Print_AS_Basic
import HasCASL.ParseItem
import HasCASL.Merge
import CASL.SymbolParser
import Logic.ParsecInterface
import Logic.Logic
import Common.AnnoState(emptyAnnos)
import Data.Dynamic
import Control.Monad.State

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data HasCASL = HasCASL deriving (Show)
instance Language HasCASL -- default definition is okay

type Sign = Env
type Morphism = ()
type HasCASL_Sublogics = ()
type Sentence = Formula
type Symbol = ()
type RawSymbol = ()

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

instance Category HasCASL Sign Morphism  

instance Sentences HasCASL Sentence () Sign Morphism Symbol

instance StaticAnalysis HasCASL BasicSpec Sentence ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol where
    basic_analysis HasCASL = Just ( \ (b, e, a) ->
		let ne = snd $ (runState (anaBasicSpec b)) e 
		    in return (ne, initialEnv, [])) 
    signature_union HasCASL = merge

instance Logic HasCASL HasCASL_Sublogics
               BasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol ()
