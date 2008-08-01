{- |
Module      :  $Header$
Description :  Instance of class Logic for the Haskell logic
Copyright   :  (c) Christian Maeder, Sonja Groening, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Here is the place where the classes 'Category', 'Syntax',
   'StaticAnalysis', 'Sentences', and 'Logic' are instantiated for
   Haskell.

   Some method implementations for 'StaticAnalysis' and 'Sentences'
   are still missing.
-}

module Haskell.Logic_Haskell
    ( Haskell(..)
    , HaskellMorphism
    , SYMB_ITEMS
    , SYMB_MAP_ITEMS
    , Haskell_Sublogics
    , Symbol
    , RawSymbol
    ) where

import Common.AS_Annotation
import Common.DefaultMorphism

import Haskell.TiPropATC()
import Haskell.HatParser
import Haskell.HatAna
import Common.Doc
import Common.DocUtils

import Logic.Logic

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

instance Sentences Haskell (TiDecl PNT) Sign HaskellMorphism Symbol where
    map_sen Haskell _m s = return s
    print_named Haskell sen =
        pretty (sentence sen) <>
        case senAttr sen of
          [] -> empty
          lab -> space <> text "{-" <+> text lab <+> text "-}"

instance StaticAnalysis Haskell HsDecls
               (TiDecl PNT)
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign
               HaskellMorphism
               Symbol RawSymbol where
    basic_analysis Haskell = Just hatAna
    empty_signature Haskell = emptySign
    signature_union Haskell s = return . addSign s
    final_union Haskell = signature_union Haskell
    inclusion Haskell = defaultInclusion isSubSign

instance Logic Haskell Haskell_Sublogics
               HsDecls (TiDecl PNT) SYMB_ITEMS SYMB_MAP_ITEMS
               Sign
               HaskellMorphism
               Symbol RawSymbol ()
