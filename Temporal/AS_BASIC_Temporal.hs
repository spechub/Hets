{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Temporal/AS_BASIC_Temporal.hs
Description :  Abstract syntax of temporal basic specifications
Copyright   :  (c) Klaus Hartke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

pretty poor abstract syntax of temporal Basic_spec, Formula, Symb_items and
Symb_map_items.
-}

module Temporal.AS_BASIC_Temporal
    (
      FORMULA (..)
    , BASIC_SPEC (..)          -- Basic Spec
    , SYMB_ITEMS (..)          -- List of symbols
    , SYMB (..)                -- Symbols
    , SYMB_MAP_ITEMS (..)      -- Symbol map
    ) where

import Common.DocUtils
import Common.Doc
import Common.Id

import Data.Data

data BASIC_SPEC = Basic_spec
                  deriving (Show, Typeable, Data)

instance GetRange BASIC_SPEC

instance Pretty BASIC_SPEC where
   pretty = text . show

data FORMULA = Formula
               deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange FORMULA

instance Pretty FORMULA where
   pretty = text . show

data SYMB_ITEMS = Symb_items
                  deriving (Show, Eq, Typeable, Data)

data SYMB = Symb_id
            deriving (Show, Eq, Typeable, Data)

data SYMB_MAP_ITEMS = Symb_map_items
                      deriving (Show, Eq, Typeable, Data)
