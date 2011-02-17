{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable
  , GeneralizedNewtypeDeriving #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for FreeCAD
Copyright   :  (c) Christian Maeder DFKI, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

dummy instance of class Logic for FreeCAD

-}

module FreeCAD.Logic_FreeCAD where

import Logic.Logic

import Common.DefaultMorphism
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.Id
import Common.Utils

import ATerm.Lib

import Common.XmlParser (XmlParseable, parseXml)

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable

import FreeCAD.As --abstract data structure in use.

data FreeCAD = FreeCAD deriving Show

instance Language FreeCAD where
  description _ = "FreeCAD object representation language"

newtype Text = Text { fromText :: String }
  deriving (Show, Eq, Ord, GetRange, Typeable, ShATermConvertible)

instance Pretty Text where
  pretty (Text s) = text s

-- use generic Category instance from Logic.Logic

instance Syntax FreeCAD Text () () where
  parse_basic_spec FreeCAD = Nothing

instance Sentences FreeCAD () Text (DefaultMorphism Text) () where
  map_sen FreeCAD _ = return
  sym_of FreeCAD _ = [Set.singleton ()]
  symmap_of FreeCAD _ = Map.empty
  sym_name FreeCAD _ = genName "FreeCAD"

instance StaticAnalysis FreeCAD Text () () () Text (DefaultMorphism Text) () ()
  where
  basic_analysis FreeCAD = Just $ \ (s, _, _) ->
    return (s, mkExtSign s, [])
  empty_signature FreeCAD = Text ""
  is_subsig FreeCAD (Text s1) (Text s2) = isInfixOf (trim s1) s2

instance Logic FreeCAD () Text () () () Text (DefaultMorphism Text) () () ()

--TODO IO, xml parser, constructors.
