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

module Logic_Haskell where

import AS_Basic_CASL
import Print_AS_Basic
import Language.Haskell.Syntax
import Language.Haskell.Pretty
import Language.Haskell.Parser
import PrettyPrint
import Pretty
import SymbolParser
import ParsecInterface
import Logic

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data Haskell = Haskell deriving (Show)
instance Language Haskell where  -- default definition is okay

instance Eq HsModule where

instance PrettyPrint HsModule where
    printText0 _ = text . prettyPrint

execParser f = 
    do s <- readFile f
       let r = parseModuleWithMode (ParseMode f) s
       putStrLn $ case r of
			 ParseOk x -> prettyPrint x
			 ParseFailed loc msg ->
			     show loc ++ ": " ++ msg
 
type Sign = HsModule
data Morphism = NoMorphism deriving Eq

instance Category Haskell Sign Morphism  
    where

-- abstract syntax, parsing (and printing)

instance Syntax Haskell HsModule
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec Haskell = Nothing
	 parse_symb_items Haskell = Just(toParseFun symbItems ())
	 parse_symb_map_items Haskell = Just(toParseFun symbMapItems ())

data Haskell_Sublogics = NoSublogic deriving (Eq, Ord)

instance LatticeWithTop Haskell_Sublogics where

type Sentence = HsDecl

data Symbol = DummySymbol deriving (Eq, Ord, Show)
data RawSymbol = DummyRawSymbol deriving (Eq, Show)

instance Sentences Haskell Sentence Sign Morphism Symbol where

instance StaticAnalysis Haskell HsModule Sentence 
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol where

instance Logic Haskell Haskell_Sublogics
               HsModule Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol where
