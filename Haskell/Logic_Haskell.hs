{-# OPTIONS -fno-warn-missing-methods #-}
-- needs -package haskell-src

{- HetCATS/Haskell/Logic_Haskell.hs
   $Id$
   Authors: C. Maeder
   Year:    2003

   Here is the place where the class Logic is instantiated for Haskell.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions

-}

module Haskell.Logic_Haskell where

import CASL.AS_Basic_CASL
import CASL.Print_AS_Basic
import Haskell.Language.Syntax
import Haskell.HParser
import CASL.SymbolParser
import Logic.ParsecInterface
import Logic.Logic
import Data.Dynamic

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data Haskell = Haskell deriving (Show)
instance Language Haskell where  -- default definition is okay

type Sign = HsDecls
type Morphism = ()

instance Typeable HsDecl

instance Category Haskell Sign Morphism  
    where

-- abstract syntax, parsing (and printing)

instance Syntax Haskell HsDecls
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec Haskell = Just(toParseFun hParser ())
	 parse_symb_items Haskell = Just(toParseFun symbItems ())
	 parse_symb_map_items Haskell = Just(toParseFun symbMapItems ())

type Haskell_Sublogics = ()

instance LatticeWithTop Haskell_Sublogics where

type Sentence = HsDecls

type Symbol = ()
type RawSymbol = ()

instance Sentences Haskell Sentence () Sign Morphism Symbol where

instance StaticAnalysis Haskell HsDecls Sentence () 
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol where

instance Logic Haskell Haskell_Sublogics
               HsDecls Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol () where
