{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances
  , OverlappingInstances #-}
{- |
Module      :  ./Haskell/Logic_Haskell.hs
Description :  Instance of class Logic for the Haskell logic
Copyright   :  (c) Christian Maeder, Sonja Groening, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

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
    ( Haskell (..)
    , HaskellMorphism
    , SYMB_ITEMS
    , SYMB_MAP_ITEMS
    , Haskell_Sublogics
    , Symbol
    , RawSymbol
    ) where

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.Doc as Doc
import Common.DocUtils
import Common.Id
import Common.Json
import Common.ToXml

import Data.Monoid

import Haskell.TiPropATC ()
import Haskell.HatParser
import Haskell.HatAna

import Logic.Logic

import Text.XML.Light

{- a dummy datatype for the LogicGraph and for identifying the right
instances -}

data Haskell = Haskell deriving Show

instance Language Haskell where
 description _ = unlines
  [ "Haskell - a purely functional programming language"
  , "featuring static typing, higher-order functions, polymorphism,"
  , "type classes and monadic effects."
  , "See http://www.haskell.org. This version is based on Programatica,"
  , "see http://www.cse.ogi.edu/PacSoft/projects/programatica/" ]

type HaskellMorphism = DefaultMorphism Sign

-- abstract syntax, parsing (and printing)

type SYMB_ITEMS = ()
type SYMB_MAP_ITEMS = ()

instance Monoid HsDecls where
    mempty = HsDecls []
    mappend (HsDecls l1) (HsDecls l2) = HsDecls $ l1 ++ l2

instance Syntax Haskell HsDecls Symbol
                SYMB_ITEMS SYMB_MAP_ITEMS
      where
         parse_basic_spec Haskell = Just $ const hatParser
         parse_symb_items Haskell = Nothing
         parse_symb_map_items Haskell = Nothing

type Haskell_Sublogics = ()

type Symbol = ()
type RawSymbol = ()

instance GetRange (TiDecl PNT)

instance ToJson (TiDecl PNT) where
  asJson _ = mkJObj []

instance ToXml (TiDecl PNT) where
  asXml _ = unode "undefined" ()

instance Sentences Haskell (TiDecl PNT) Sign HaskellMorphism Symbol where
    map_sen Haskell _m = return
    print_named Haskell sen =
        pretty (sentence sen) Doc.<>
        case senAttr sen of
          [] -> empty
          lab -> space Doc.<> text "{-" <+> text lab <+> text "-}"

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
    is_subsig Haskell = isSubSign
    subsig_inclusion Haskell = defaultInclusion

instance Logic Haskell Haskell_Sublogics
               HsDecls (TiDecl PNT) SYMB_ITEMS SYMB_MAP_ITEMS
               Sign
               HaskellMorphism
               Symbol RawSymbol ()
