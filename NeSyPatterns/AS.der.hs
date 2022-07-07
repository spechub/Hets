{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./NeSyPatterns/AS.der.hs
Description :  Abstract syntax for neural-symbolic patterns
Copyright   :  (c) Till Mossakowski, Uni Magdeburg 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till.mossakowski@pvgu.de
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for neural-symbolic patterns
-}

{-
  Ref.
  van Bekkum, M., de Boer, M., van Harmelen, F. et al.
  Modular design patterns for hybrid learning and reasoning systems.
  Appl Intell 51, 6528–6546 (2021). https://doi.org/10.1007/s10489-021-02394-3
-}

module NeSyPatterns.AS where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.AS_Annotation as AS_Anno

import Data.Data

-- DrIFT command
{-! global: GetRange !-}

-- | nodes are of form: ontology_term[id]
-- | both components are optional, but at least one must be present
data Node = Node {
    ontologyTerm :: (Maybe Id.Token),
    nesyId :: (Maybe Id.Token),
    nodeRange :: Id.Range
  } deriving (Show, Typeable, Data, Eq, Ord)
newtype BASIC_SPEC = Basic_spec { items :: [AS_Anno.Annoted BASIC_ITEM] }
                  deriving (Show, Typeable, Data)

data BASIC_ITEM = Path {
    path ::  [Node] -- written node -> ... -> node;
  }
    deriving (Show, Typeable, Data)


newtype SYMB = Symb_id Id.Token
            deriving (Show, Eq, Ord, Typeable, Data)

data SYMB_ITEMS = Symb_items [SYMB] Id.Range
                  deriving (Show, Eq, Ord, Typeable, Data)

data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP] Id.Range
                      deriving (Show, Eq, Ord, Typeable, Data)

data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB Id.Range
                   -- pos: "|->"
                   deriving (Show, Eq, Ord, Typeable, Data)
