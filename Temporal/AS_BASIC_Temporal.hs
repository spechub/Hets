{- |
Module      :  $Header$
Description :  Abstract syntax of temporal basic specifications
Copyright   :  (c) Klaus Hartke, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Abstract syntax of temporal Basic_spec, Formula, Symb_items and Symb_map_items.
-}

module Temporal.AS_BASIC_Temporal
    (
      FORMULA(..)
    , BASIC_SPEC (..)          -- Basic Spec
    , SYMB_ITEMS (..)          -- List of symbols
    , SYMB (..)                -- Symbols
    , SYMB_MAP_ITEMS (..)      -- Symbol map
    ) where

import Common.DocUtils
import Common.Doc
import Common.Id

data BASIC_SPEC = Basic_spec
                  deriving Show

instance GetRange BASIC_SPEC

instance Pretty BASIC_SPEC where
   pretty = text . show

data FORMULA = Formula
               deriving (Show, Eq, Ord)

instance Pretty FORMULA where
   pretty = text . show

data SYMB_ITEMS = Symb_items
                  deriving (Show, Eq)

data SYMB = Symb_id
            deriving (Show, Eq)

data SYMB_MAP_ITEMS = Symb_map_items
                      deriving (Show, Eq)

