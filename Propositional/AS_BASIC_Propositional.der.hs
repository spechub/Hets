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
    ( FORMULA (..)             -- datatype for Propositional Formulas
    , BASIC_ITEMS (..)         -- Items of a Basic Spec
    , BASIC_SPEC (..)          -- Basic Spec
    , SYMB_ITEMS (..)          -- List of symbols
    , SYMB (..)                -- Symbols
    , SYMB_MAP_ITEMS (..)      -- Symbol map
    , SYMB_OR_MAP (..)         -- Symbol or symbol map
    , PRED_ITEM (..)           -- Predicates
    , isPrimForm
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
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
data FORMULA =
    False_atom Id.Range
    -- pos: "False
  | True_atom Id.Range
    -- pos: "True"
  | Predication Id.Token
    -- pos: Propositional Identifiers
  | Negation FORMULA Id.Range
    -- pos: not
  | Conjunction [FORMULA] Id.Range
    -- pos: "/\"s
  | Disjunction [FORMULA] Id.Range
    -- pos: "\/"s
  | Implication FORMULA FORMULA Id.Range
    -- pos: "=>"
  | Equivalence FORMULA FORMULA Id.Range
    -- pos: "<=>"
    deriving (Show, Eq, Ord)

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

isPrimForm :: FORMULA -> Bool
isPrimForm f = case f of
        True_atom _ -> True
        False_atom _ -> True
        Predication _ -> True
        Negation _ _ -> True
        _ -> False

-- Pretty printing for formulas
printFormula :: FORMULA -> Doc
printFormula frm =
  let ppf p f = (if p f then id else parens) $ printFormula f
      isJunctForm f = case f of
        Implication _ _ _ -> False
        Equivalence _ _ _ -> False
        _ -> True
  in case frm of
  False_atom _ -> text falseS
  True_atom _ -> text trueS
  Predication x -> pretty x
  Negation f _ -> notDoc <+> ppf isPrimForm f
  Conjunction xs _ -> sepByArbitrary andDoc $ map (ppf isPrimForm) xs
  Disjunction xs _ -> sepByArbitrary orDoc $ map (ppf isPrimForm) xs
  Implication x y _ -> ppf isJunctForm x <+> implies <+> ppf isJunctForm y
  Equivalence x y _ -> ppf isJunctForm x <+> equiv <+> ppf isJunctForm y

sepByArbitrary :: Doc -> [Doc] -> Doc
sepByArbitrary d = fsep . prepPunctuate (d <> space)

printPredItem :: PRED_ITEM -> Doc
printPredItem (Pred_item xs _) = fsep $ map pretty xs

printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: BASIC_ITEMS -> Doc
printBasicItems (Axiom_items xs) = vcat $ map pretty xs
printBasicItems (Pred_decl x) = pretty x

printSymbol :: SYMB -> Doc
printSymbol (Symb_id sym) = pretty sym

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items xs _) = fsep $ map pretty xs

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap (Symb sym) = pretty sym
printSymbOrMap (Symb_map source dest  _) =
  pretty source <+> mapsto <+> pretty dest

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items xs _) = fsep $ map pretty xs
