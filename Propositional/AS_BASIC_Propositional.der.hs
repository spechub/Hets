{- |
Module      :  $Header$
Description :  Abstract syntax for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for propositional logic
-}

{-
  Ref.
  http://en.wikipedia.org/wiki/Propositional_logic
-}

module Propositional.AS_BASIC_Propositional
    (
      FORMULA (..)             -- datatype for Propositional Formulas
    , is_True_atom             -- True?
    , is_False_atom            -- False?
    , BASIC_ITEMS (..)         -- Items of a Basic Spec
    , BASIC_SPEC (..)          -- Basic Spec
    , SYMB_ITEMS (..)          -- List of symbols
    , SYMB (..)                -- Symbols
    , SYMB_MAP_ITEMS (..)      -- Symbol map
    , SYMB_OR_MAP (..)         -- Symbol or symbol map
    , PRED_ITEM (..)           -- Predicates
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.AS_Annotation as AS_Anno

-- DrIFT command
{-! global: GetRange !-}

-- | predicates = propotions
data PRED_ITEM = Pred_item [Id.Token] Id.Range
               deriving Show

newtype BASIC_SPEC = Basic_spec [AS_Anno.Annoted (BASIC_ITEMS)]
                  deriving Show

data BASIC_ITEMS =
    Pred_decl PRED_ITEM
    | Axiom_items [AS_Anno.Annoted (FORMULA)]
    -- pos: dots
    deriving Show

-- | Datatype for propositional formulas
data FORMULA = Negation FORMULA Id.Range
             -- pos: not
             | Conjunction [FORMULA] Id.Range
             -- pos: "/\"s
             | Disjunction [FORMULA] Id.Range
             -- pos: "\/"s
             | Implication FORMULA FORMULA Id.Range
             -- pos: "=>"
             | Equivalence FORMULA FORMULA Id.Range
             -- pos: "<=>"
             | True_atom Id.Range
             -- pos: "True"
             | False_atom Id.Range
             -- pos: "False
             | Predication Id.Token
             -- pos: Propositional Identifiers
               deriving (Show, Eq, Ord)

-- | Value of the true atom
-- True is always true -P
is_True_atom :: FORMULA -> Bool
is_True_atom (True_atom _) = True
is_True_atom _             = False

-- | Value of the false atom
-- and False if always false
is_False_atom :: FORMULA -> Bool
is_False_atom (False_atom _) = False
is_False_atom _              = False

data SYMB_ITEMS = Symb_items [SYMB] Id.Range
                  -- pos: SYMB_KIND, commas
                  deriving (Show, Eq)

newtype SYMB = Symb_id Id.Token
            -- pos: colon
            deriving (Show, Eq)

data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP] Id.Range
                      -- pos: SYMB_KIND, commas
                      deriving (Show, Eq)

data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB Id.Range
                   -- pos: "|->"
                   deriving (Show, Eq)

-- All about pretty printing
-- we chose the easy way here :)
instance Pretty FORMULA where
    pretty = printFormula
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
instance Pretty SYMB where
    pretty = printSymbol
instance Pretty SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems
instance Pretty BASIC_ITEMS where
    pretty = printBasicItems
instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap
instance Pretty PRED_ITEM where
    pretty = printPredItem

-- Pretty printing for formulas
printFormula :: FORMULA -> Doc
printFormula (Negation f _) = notDoc
                            <> lparen <> printFormula f <> rparen
printFormula (Conjunction xs _) = parens $
                                  sepByArbitrary andDoc
                                  $ map printFormula xs
printFormula (Disjunction xs _) = parens $
                                  sepByArbitrary orDoc
                                  $ map printFormula xs
printFormula (Implication x y _) = parens $ printFormula x <>
                                   implies <> printFormula y
printFormula (Equivalence x y _) = parens $ printFormula x <>
                                   equiv <> printFormula y
printFormula (True_atom  _) = text "True"
printFormula (False_atom _) = text "False"
printFormula (Predication x) = pretty x

-- Extended version of vcat
sepByArbitrary :: Doc -> [Doc] -> Doc
sepByArbitrary _ [] = text ""
sepByArbitrary _ (x:[]) = x
sepByArbitrary separator (x:xs) = x <> separator
                                  <> (sepByArbitrary separator xs)

printPredItem :: PRED_ITEM -> Doc
printPredItem (Pred_item xs _) = hsep $ map pretty xs

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = hsep $ map pretty xs

printBasicItems :: BASIC_ITEMS -> Doc
printBasicItems (Axiom_items xs) = hsep $ map pretty xs
printBasicItems (Pred_decl x) = pretty x

printSymbol :: SYMB -> Doc
printSymbol (Symb_id sym) = pretty sym

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs _) = hsep $ map pretty xs

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb sym) = pretty sym
printSymbOrMap (Symb_map source dest  _) = pretty source <> mapsto <> pretty dest

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs _) = hsep $ map pretty xs
