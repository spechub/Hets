{-| 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Sonja Groening, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   Here is the place where the class Logic is instantiated for Haskell.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions

-}

module Haskell.Logic_Haskell (Haskell(..)) where

import Data.Dynamic            
import Common.DynamicUtils 

import Common.Result                     (Result (..))
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.AS_Annotation
import Common.ATerm.Conversion

-- import Haskell.ATC_Haskell      -- generated ATerm conversions
import Haskell.HatParser                 (HsDecls,
                                          hatParser)
import Haskell.HatAna

import Logic.Logic             

hsDeclsTc :: TyCon
hsDeclsTc = mkTyCon "Haskell.HatParser.HsDecls"

instance ATermConvertible HsDecls

instance Typeable HsDecls where
    typeOf _ = mkTyConApp hsDeclsTc []

instance PrintLaTeX HsDecls where
  printLatex0 = printText0

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances

data Haskell = Haskell deriving (Show)
instance Language Haskell where
 description _ = 
  "Haskell - a purely functional programming language,\ 
  \featuring static typing, higher-order functions, polymorphism, type classes and monadic effects\ 
  \See http://www.haskell.org"

type Morphism = ()

instance Category Haskell Sign Morphism where
  dom Haskell _ = empty_signature Haskell

-- abstract syntax, parsing (and printing)

type SYMB_ITEMS = ()
type SYMB_MAP_ITEMS = ()

instance Syntax Haskell HsDecls
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec Haskell = Just hatParser
	 parse_symb_items Haskell = Nothing
	 parse_symb_map_items Haskell = Nothing

type Haskell_Sublogics = ()

type Symbol = ()
type RawSymbol = ()

instance Sentences Haskell Sentence () Sign Morphism Symbol where
    map_sen Haskell _m s = return s
    print_named Haskell ga (NamedSen lab sen) = printText0 ga sen <>
	if null lab then empty 
	else space <> text "{-" <+> text lab <+> text "-}" 
    provers Haskell = [] 
    cons_checkers Haskell = []

instance StaticAnalysis Haskell HsDecls
               Sentence () 
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol where
    basic_analysis Haskell = Just hatAna 
    empty_signature Haskell = emptyEnv
    final_union Haskell = signature_union Haskell

instance Logic Haskell Haskell_Sublogics
               HsDecls Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol ()
