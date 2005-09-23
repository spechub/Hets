{-| 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Sonja Groening, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Here is the place where the classes 'Category', 'Syntax',
   'StaticAnalysis', 'Sentences', and 'Logic' are instantiated for
   Haskell.

   Some method implementations for 'StaticAnalysis' and 'Sentences'
   are still missing.  -}

module Haskell.Logic_Haskell 
    (Haskell(..), 
     HaskellMorphism,
     SYMB_ITEMS,
     SYMB_MAP_ITEMS, 
     Haskell_Sublogics,
     Symbol,
     RawSymbol) where

import Data.Dynamic            
import Common.DynamicUtils 

import Common.PrettyPrint
import Common.Lib.Pretty
import Common.AS_Annotation
import Common.DefaultMorphism

import Haskell.TiATC()
import Haskell.HatParser                
import Haskell.HatAna

import Logic.Logic             

hsDeclsTc :: TyCon
hsDeclsTc = mkTyCon "Haskell.HatParser.HsDecls"

instance Typeable HsDecls where
    typeOf _ = mkTyConApp hsDeclsTc []

tyconSign :: TyCon
tyconSign = mkTyCon "Haskell.HatAna.Sign"

instance Typeable Sign where
  typeOf _ = mkTyConApp tyconSign []

tyconPNT :: TyCon
tyconPNT = mkTyCon "Haskell.HatAna.PNT"

instance Typeable PNT where
  typeOf _ = mkTyConApp tyconPNT []

hsDeclItc :: TyCon
hsDeclItc = mkTyCon "Haskell.HatAna.TiDecl"

instance Typeable i => Typeable (TiDecl i) where 
  typeOf s = mkTyConApp hsDeclItc [typeOf $ (undefined :: TiDecl a -> a) s]

instance PrintLaTeX HsDecls where
  printLatex0 = printText0

instance PrintLaTeX Sign where
     printLatex0 = printText0

instance PrintLaTeX (TiDecl PNT) where
     printLatex0 = printText0

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances

data Haskell = Haskell deriving (Show)
instance Language Haskell where
 description _ = 
  "Haskell - a purely functional programming language,\ 
  \ featuring static typing, higher-order functions, polymorphism,\ 
  \ type classes and monadic effects.\ 
  \ See http://www.haskell.org. This version is based on Programatica,\ 
  \ see http://www.cse.ogi.edu/PacSoft/projects/programatica/"

type HaskellMorphism = DefaultMorphism Sign

instance Category Haskell Sign HaskellMorphism where
  dom Haskell = domOfDefaultMorphism
  cod Haskell = codOfDefaultMorphism
  ide Haskell = ideOfDefaultMorphism
  comp Haskell = compOfDefaultMorphism
  legal_obj Haskell = const True
  legal_mor Haskell = legalDefaultMorphism (legal_obj Haskell)

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

instance Sentences Haskell (TiDecl PNT) () Sign HaskellMorphism Symbol where
    map_sen Haskell _m s = return s
    print_named Haskell ga s = printText0 ga sen <>
	if null lab then empty 
	else space <> text "{-" <+> text lab <+> text "-}" 
        where lab = senName s
              sen = sentence s

    provers Haskell = [] 
    cons_checkers Haskell = []

instance StaticAnalysis Haskell HsDecls
               (TiDecl PNT) () 
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               HaskellMorphism 
               Symbol RawSymbol where
    basic_analysis Haskell = Just hatAna 
    empty_signature Haskell = emptySign
    signature_union Haskell s = return . addSign s
    final_union Haskell = signature_union Haskell
    inclusion Haskell = defaultInclusion (is_subsig Haskell)
    is_subsig Haskell = isSubSign

instance Logic Haskell Haskell_Sublogics
               HsDecls (TiDecl PNT) SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               HaskellMorphism
               Symbol RawSymbol ()
