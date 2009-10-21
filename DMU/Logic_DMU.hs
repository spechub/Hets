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

import Common.AS_Annotation
import Common.DefaultMorphism
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

newtype Text = Text String
  deriving (Show, Eq, Ord, Pretty, GetRange, Typeable, ShATermConvertible)

-- use generic Category instance from Logic.Logic

instance Syntax DMU Text () () where
  parse_basic_spec DMU = Just $ fmap Text $ many1 anyChar

instance Sentences DMU Text () (DefaultMorphism ()) () where
  map_sen DMU _ = return
  sym_of DMU _ = Set.singleton ()
  symmap_of DMU _ = Map.empty
  sym_name DMU _ = genName "DMU"

instance StaticAnalysis DMU Text Text () () () (DefaultMorphism ()) () () where
  basic_analysis DMU = Just $ \ (s, _, _) ->
    return (s, mkExtSign (), [makeNamed "DMU" s])
  empty_signature DMU = ()

instance Logic DMU () Text Text () () () (DefaultMorphism ()) () () ()
