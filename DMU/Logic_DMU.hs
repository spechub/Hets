{- |
Module      :  $Header$
Description :  Instance of class Logic for DMU
Copyright   :  (c) Christian Maeder DFKI, Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import ATerm.Lib

import Text.ParserCombinators.Parsec

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Typeable

data DMU = DMU deriving Show

instance Language DMU where
  description _ = "wrap Catia ouput"

newtype Text = Text { fromText :: String }
  deriving (Show, Eq, Ord, GetRange, Typeable, ShATermConvertible)

instance Pretty Text where
  pretty (Text s) = text s

-- use generic Category instance from Logic.Logic

instance Syntax DMU Text () () where
  parse_basic_spec DMU = Just $ fmap Text $ many1 anyChar

instance Sentences DMU () Text (DefaultMorphism Text) () where
  map_sen DMU _ = return
  sym_of DMU _ = Set.singleton ()
  symmap_of DMU _ = Map.empty
  sym_name DMU _ = genName "DMU"

instance StaticAnalysis DMU Text () () () Text (DefaultMorphism Text) () ()
  where
  basic_analysis DMU = Just $ \ (s, _, _) ->
    return (s, mkExtSign s, [])
  empty_signature DMU = Text ""

instance Logic DMU () Text () () () Text (DefaultMorphism Text) () () ()
