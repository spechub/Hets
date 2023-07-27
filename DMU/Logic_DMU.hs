{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable
  , GeneralizedNewtypeDeriving, DeriveGeneric #-}
{- |
Module      :  ./DMU/Logic_DMU.hs
Description :  Instance of class Logic for DMU
Copyright   :  (c) Christian Maeder DFKI, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

dummy instance of class Logic for DMU

-}

module DMU.Logic_DMU where

import Logic.Logic

import Common.DefaultMorphism
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.Id
import Common.Utils

import ATerm.Lib

import Text.ParserCombinators.Parsec

import Data.List
import Data.Monoid ()
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable
import GHC.Generics

data DMU = DMU deriving Show

instance Language DMU where
  description _ = "a logic to wrap output of the CAD tool Catia"

newtype Text = Text { fromText :: String }
  deriving (Show, Eq, Ord, GetRange, Typeable, ShATermConvertible, Generic)

instance Pretty Text where
  pretty (Text s) = text s

-- use generic Category instance from Logic.Logic

instance Semigroup Text where
    (Text l1) <> (Text l2) = Text
      . unlines $ lines l1 ++ lines l2
instance Monoid Text where
    mempty = Text ""

instance Syntax DMU Text () () () where
  parse_basic_spec DMU = Just (\ _ -> fmap Text $ many1 anyChar)

instance Sentences DMU () Text (DefaultMorphism Text) () where
  map_sen DMU _ = return
  sym_of DMU _ = [Set.singleton ()]
  symmap_of DMU _ = Map.empty
  sym_name DMU _ = genName "DMU"

instance StaticAnalysis DMU Text () () () Text (DefaultMorphism Text) () ()
  where
  basic_analysis DMU = Just $ \ (s, _, _) ->
    return (s, mkExtSign s, [])
  empty_signature DMU = Text ""
  is_subsig DMU (Text s1) (Text s2) = isInfixOf (trim s1) s2

instance Logic DMU () Text () () () Text (DefaultMorphism Text) () () ()
