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

module Logic_HasCASL where

import As
import AS_Basic_CASL(SYMB_ITEMS, SYMB_MAP_ITEMS)
import PrintAs
import Print_AS_Basic
import ParseItem
import SymbolParser
import ParsecInterface
import Logic
import AnnoState(emptyAnnos)
import Dynamic

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data HasCASL = HasCASL deriving (Show)
instance Language HasCASL where  -- default definition is okay

type Sign = BasicSpec
data Morphism = NoMorphism deriving (Eq, Show)

instance Category HasCASL Sign Morphism  
    where

-- abstract syntax, parsing (and printing)

instance Syntax HasCASL BasicSpec
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec HasCASL = Just(toParseFun basicSpec emptyAnnos)
	 parse_symb_items HasCASL = Just(toParseFun symbItems ())
	 parse_symb_map_items HasCASL = Just(toParseFun symbMapItems ())

data HasCASL_Sublogics = NoSublogic deriving (Eq, Ord, Show)

instance LatticeWithTop HasCASL_Sublogics where

type Sentence = Formula

data Symbol = DummySymbol deriving (Eq, Ord, Show)
data RawSymbol = DummyRawSymbol deriving (Eq, Show)

instance Sentences HasCASL Sentence () Sign Morphism Symbol where

instance StaticAnalysis HasCASL BasicSpec Sentence ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol where

instance Typeable HasCASL_Sublogics where
  typeOf _ = mkAppTy (mkTyCon "HasCASL_Sublogics") []
instance Typeable BasicSpec where
  typeOf _ = mkAppTy (mkTyCon "BasicSpec") []
instance Typeable Sentence where
  typeOf _ = mkAppTy (mkTyCon "Sentence") []
instance Typeable Morphism where
  typeOf _ = mkAppTy (mkTyCon "Morphism") []
instance Typeable Symbol where
  typeOf _ = mkAppTy (mkTyCon "Symbol") []
instance Typeable RawSymbol where
  typeOf _ = mkAppTy (mkTyCon "RawSymbol") []

instance Logic HasCASL HasCASL_Sublogics
               BasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol () where
