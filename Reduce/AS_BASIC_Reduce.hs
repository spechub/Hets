{-# LINE 1 "Reduce/AS_BASIC_Reduce.hs" #-}
{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

This file contains the abstract syntax for the reduce computer algebra system as well as pretty printer for it.

-}

module Reduce.AS_BASIC_Reduce
    (
     EXPRESSION (..)          -- datatype for numerical expressions (e.g. polynomials)
    , BASIC_ITEMS (..)         -- Items of a Basic Spec
    , BASIC_SPEC (..)          -- Basic Spec
    , SYMB_ITEMS (..)          -- List of symbols
    , SYMB (..)                -- Symbols
    , SYMB_MAP_ITEMS (..)      -- Symbol map
    , SYMB_OR_MAP (..)         -- Symbol or symbol map
    , OP_ITEM (..)             -- operator declaration
    , VAR_ITEM (..)            -- variable declaration (needed?)
    , CMD (..)
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
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
    | Axiom_item (AS_Anno.Annoted CMD)
    deriving Show

-- | Datatype for expressions
data EXPRESSION =
    Var Id.Token
  | Op String [EXPRESSION] Id.Range          -- token instead string Id vs Token:
  | List [EXPRESSION] Id.Range
  | Int Int Id.Range
  | Double Float Id.Range
  deriving (Eq, Ord, Show)

data CMD =
    Cmd String [EXPRESSION]
    | Repeat EXPRESSION EXPRESSION [CMD] -- accuracy, variable, statements
    deriving (Show, Eq, Ord)

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

instance Pretty OP_ITEM where
    pretty = printOpItem
instance Pretty VAR_ITEM where
    pretty = printVarItem
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty BASIC_ITEMS where
    pretty = printBasicItems
instance Pretty EXPRESSION where
    pretty = printExpression
instance Pretty SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty SYMB where
    pretty = printSymbol
instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems
instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap
instance Pretty CMD where
    pretty = printCMD

printCMD :: CMD -> Doc
printCMD (Cmd s exps) = (text s) <> (parens (sepByCommas (map printExpression exps)))

printExpression :: EXPRESSION -> Doc
printExpression (Var token) = text (tokStr token)
printExpression (Op s exps _) = text s <+> (parens (sepByCommas (map printExpression exps)))
printExpression (List exps _) = sepByCommas (map printExpression exps)
printExpression (Int i _) = text (show i)
printExpression (Double d _) = text (show d)

printOpItem :: OP_ITEM -> Doc
printOpItem (Op_item tokens _) = (text "operator") <+> (sepByCommas (map pretty tokens))

printVarItem :: VAR_ITEM -> Doc
printVarItem (Var_item vars _) = (text "var") <+> (sepByCommas (map pretty vars))

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: BASIC_ITEMS -> Doc
printBasicItems (Axiom_item x) = pretty x
printBasicItems (Op_decl x) = pretty x

printSymbol :: SYMB -> Doc
printSymbol (Symb_id sym) = pretty sym

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs _) = fsep $ map pretty xs

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb sym) = pretty sym
printSymbOrMap (Symb_map source dest _) =
  pretty source <+> mapsto <+> pretty dest

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs _) = fsep $ map pretty xs


-- Instances for GetRange

instance GetRange OP_ITEM where
  getRange = const nullRange
  rangeSpan x = case x of
    Op_item a b -> joinRanges [rangeSpan a, rangeSpan b]

instance GetRange VAR_ITEM where
  getRange = const nullRange
  rangeSpan x = case x of
    Var_item a b -> joinRanges [rangeSpan a, rangeSpan b]


instance GetRange BASIC_SPEC where
  getRange = const nullRange
  rangeSpan x = case x of
    Basic_spec a -> joinRanges [rangeSpan a]

instance GetRange BASIC_ITEMS where
  getRange = const nullRange
  rangeSpan x = case x of
    Op_decl a -> joinRanges [rangeSpan a]
-- Var_decl a -> joinRanges [rangeSpan a]
    Axiom_item a -> joinRanges [rangeSpan a]

instance GetRange CMD where
    getRange = const nullRange
    rangeSpan (Cmd _ exps) = joinRanges (map rangeSpan exps)

instance GetRange SYMB_ITEMS where
  getRange = const nullRange
  rangeSpan x = case x of
    Symb_items a b -> joinRanges [rangeSpan a, rangeSpan b]

instance GetRange SYMB where
  getRange = const nullRange
  rangeSpan x = case x of
    Symb_id a -> joinRanges [rangeSpan a]

instance GetRange SYMB_MAP_ITEMS where
  getRange = const nullRange
  rangeSpan x = case x of
    Symb_map_items a b -> joinRanges [rangeSpan a, rangeSpan b]

instance GetRange SYMB_OR_MAP where
  getRange = const nullRange
  rangeSpan x = case x of
    Symb a -> joinRanges [rangeSpan a]
    Symb_map a b c -> joinRanges [rangeSpan a, rangeSpan b, rangeSpan c]

instance GetRange EXPRESSION where
  getRange = const nullRange
  rangeSpan x = case x of
                      Var token -> joinRanges [rangeSpan token]
                      Op _ exps a -> joinRanges $ [rangeSpan a] ++ (map rangeSpan exps)
                      List exps a -> joinRanges $ [rangeSpan a] ++ (map rangeSpan exps)
                      Int _ a -> joinRanges [rangeSpan a]
                      Double _ a -> joinRanges [rangeSpan a]
