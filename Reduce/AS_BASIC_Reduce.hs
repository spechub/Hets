{-# LINE 1 "Reduce/AS_BASIC_Reduce.der.hs" #-}
{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for reduce computer algebra system
-}

module Reduce.AS_BASIC_Reduce
    ( FORMULA (..)             -- datatype for Propositional Formulas
    , EXPRESSION (..)
    , BASIC_ITEMS (..)         -- Items of a Basic Spec
    , BASIC_SPEC (..)          -- Basic Spec
    , SYMB_ITEMS (..)          -- List of symbols
    , SYMB (..)                -- Symbols
    , SYMB_MAP_ITEMS (..)      -- Symbol map
    , SYMB_OR_MAP (..)         -- Symbol or symbol map
    , OP_ITEM (..)             -- 
    , VAR_ITEM (..)
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.AS_Annotation as AS_Anno

-- | operator symbol declaration
data OP_ITEM = Op_item [Id.Token] Id.Range
               deriving Show

-- | variable symbol declaration
data VAR_ITEM = Var_item [Id.Token] Id.Range
                deriving Show

newtype BASIC_SPEC = Basic_spec [AS_Anno.Annoted (BASIC_ITEMS)]
                  deriving Show

-- | basic items: either an operator declaration or and axiom
data BASIC_ITEMS =
    Op_decl OP_ITEM
    | Var_decl VAR_ITEM
    | Axiom_items [AS_Anno.Annoted (FORMULA)]
    deriving Show

-- | Datatype for expressions
data EXPRESSION = 
    Var String Id.Range
  | Op [EXPRESSION] Id.Range
  | List [EXPRESSION] Id.Range
  | Int Int
  | Double Double
  deriving (Eq,Show)
  
-- | Datatyoe for nary boolean expressions
data Naryboolop = And | Or | Cmd deriving (Eq,Show)

-- | Datatype for binary bollean expressions
data Bboolop = Impl | Repl | Equiv deriving (Eq,Show)


-- | Datatype for reduce formulas (could be factored)
data FORMULA =
    False_atom Id.Range
  | True_atom Id.Range
  | Nary Naryboolop  [FORMULA] Id.Range
  | Binary Bboolop FORMULA FORMULA Id.Range
    deriving (Show, Eq)

-- | symbol lists for hiding
data SYMB_ITEMS = Symb_items [SYMB] Id.Range
                  -- pos: SYMB_KIND, commas
                  deriving (Show, Eq)

-- | symbol for identifiers
newtype SYMB = Symb_id Id.Token
            -- pos: colon
            deriving (Show, Eq)

-- | symbol maps for renamings
data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP] Id.Range
                      -- pos: SYMB_KIND, commas
                      deriving (Show, Eq)

-- | symbol map or renaming (renaming then denotes the identity renaming
data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB Id.Range
                   -- pos: "|->"
                   deriving (Show, Eq)

-- Pretty Printing; 



-- Instances for GetRange

instance GetRange FORMULA where
  getRange = const nullRange
  rangeSpan x = case x of 
                  False_atom a -> joinRanges [rangeSpan a]
                  True_atom a -> joinRanges [rangeSpan a]
                  Nary op formulas a -> joinRanges [rangeSpan a, rangeSpan formulas]
                  Binary bop formula1 formula2 a -> joinRanges [rangeSpan a, rangeSpan formula1, rangeSpan formula2]

instance GetRange OP_ITEM where
  getRange = const nullRange
  rangeSpan x = case x of
    Op_item a b -> joinRanges [rangeSpan a,rangeSpan b]

instance GetRange VAR_ITEM where
  getRange = const nullRange
  rangeSpan x = case x of
    Var_item a b -> joinRanges [rangeSpan a,rangeSpan b]


instance GetRange BASIC_SPEC where
  getRange = const nullRange
  rangeSpan x = case x of
    Basic_spec a -> joinRanges [rangeSpan a]

instance GetRange BASIC_ITEMS where
  getRange = const nullRange
  rangeSpan x = case x of
    Op_decl a -> joinRanges [rangeSpan a]
    Var_decl a -> joinRanges [rangeSpan a]
    Axiom_items a -> joinRanges [rangeSpan a]

-- instance GetRange FORMULA 

instance GetRange SYMB_ITEMS where
  getRange = const nullRange
  rangeSpan x = case x of
    Symb_items a b -> joinRanges [rangeSpan a,rangeSpan b]

instance GetRange SYMB where
  getRange = const nullRange
  rangeSpan x = case x of
    Symb_id a -> joinRanges [rangeSpan a]

instance GetRange SYMB_MAP_ITEMS where
  getRange = const nullRange
  rangeSpan x = case x of
    Symb_map_items a b -> joinRanges [rangeSpan a,rangeSpan b]

instance GetRange SYMB_OR_MAP where
  getRange = const nullRange
  rangeSpan x = case x of
    Symb a -> joinRanges [rangeSpan a]
    Symb_map a b c -> joinRanges [rangeSpan a,rangeSpan b,rangeSpan c]
