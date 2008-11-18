module Temporal.AS_BASIC_Temporal
    (
      FORMULA(..)
    , BASIC_SPEC (..)          -- Basic Spec
    , SYMB_ITEMS (..)          -- List of symbols
    , SYMB (..)                -- Symbols
    , SYMB_MAP_ITEMS (..)      -- Symbol map
    ) where

data BASIC_SPEC = Basic_spec
                  deriving Show

data FORMULA = Formula
               deriving Show

data SYMB_ITEMS = Symb_items
                  deriving (Show, Eq)

data SYMB = Symb_id
            deriving (Show, Eq)

data SYMB_MAP_ITEMS = Symb_map_items
                      deriving (Show, Eq)

