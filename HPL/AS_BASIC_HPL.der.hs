{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./HPL/AS_BASIC_HPL.der.hs
Description :  Abstract syntax for hybrid propositional logic
Copyright   :  (c) Mihai Codescu, IMAR, 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for hybrid propositional logic
-}

module HPL.AS_BASIC_HPL
    ( FORMULA (..)             -- datatype for Propositional Formulas
    , BASIC_ITEMS (..)         -- Items of a Basic Spec
    , BASIC_SPEC (..)          -- Basic Spec
    --, SYMB_ITEMS (..)          -- List of symbols
    --, SYMB (..)                -- Symbols
    --, SYMB_MAP_ITEMS (..)      -- Symbol map
    --, SYMB_OR_MAP (..)         -- Symbol or symbol map
    , NOM_ITEM (..)              -- nominals
    --, isPrimForm
    ) where

import Common.Id as Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.AS_Annotation as AS_Anno

import Data.Data
import qualified Propositional.AS_BASIC_Propositional as PBasic

-- DrIFT command
{-! global: GetRange !-}

-- | predicates = propotions
data NOM_ITEM = Nom_item [Id.Token] Id.Range
               deriving (Show, Typeable, Data)

newtype BASIC_SPEC = Basic_spec [AS_Anno.Annoted BASIC_ITEMS]
                  deriving (Show, Typeable, Data)

data BASIC_ITEMS =
      Pred_decl PBasic.PRED_ITEM
    | Nom_decl NOM_ITEM
    | Axiom_items [AS_Anno.Annoted FORMULA]
    -- pos: dots
    deriving (Show, Typeable, Data)

-- | Datatype for hybrid propositional formulas
-- we need logical connectives between arbitrary hybrid formulas
-- so we need to cover these cases too
-- does this lead to parsing ambiguities? 
-- no: we can always have connectives at the global level
-- and only predications are from the basic level
-- at parsing time!
-- maybe in the case of quantifications for FOL we can have trouble
data FORMULA =
  Prop_formula PBasic.FORMULA 
   -- propositional sentences
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
  | Nominal Id.Token Id.Range 
   -- nominals as sentences
  | AtState Id.Token FORMULA Id.Range
   -- at_i formulas
  | BoxFormula FORMULA Id.Range
   -- pos: "<>"
  | DiamondFormula FORMULA Id.Range
   -- pos: "[]"
    deriving (Show, Eq, Ord, Typeable, Data)

{-
I guess this can stay from Prop
data SYMB_ITEMS = Symb_items [SYMB] Id.Range
                  -- pos: SYMB_KIND, commas
                  deriving (Show, Eq, Ord, Typeable, Data)

newtype SYMB = Symb_id Id.Token
            -- pos: colon
            deriving (Show, Eq, Ord, Typeable, Data)

data SYMB_MAP_ITEMS = Symb_map_items [SYMB_OR_MAP] Id.Range
                      -- pos: SYMB_KIND, commas
                      deriving (Show, Eq, Ord, Typeable, Data)

data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB Id.Range
                   -- pos: "|->"
                   deriving (Show, Eq, Ord, Typeable, Data)
-}

{- All about pretty printing
we chose the easy way here :) -}
instance Pretty FORMULA where
    pretty = printFormula
instance Pretty BASIC_SPEC where
    pretty = printBasicSpec
{-
instance Pretty SYMB where
    pretty = printSymbol
instance Pretty SYMB_ITEMS where
    pretty = printSymbItems
instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems
instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap
-}
instance Pretty BASIC_ITEMS where
    pretty = printBasicItems
instance Pretty NOM_ITEM where
    pretty = printNomItem

-- Pretty printing for formulas, TODO: see other functions needed for pretty printing in Prop
printFormula :: FORMULA -> Doc
printFormula aFrm =
  case aFrm of
   Prop_formula pfrm -> PBasic.printFormula pfrm 
   Nominal nom _ -> pretty nom  
   AtState nom frm _ -> prettyAt <+> pretty nom <+> colon <+> printFormula frm 
   BoxFormula frm _ -> boxDoc <+> printFormula frm
   DiamondFormula frm _ -> diamondDoc <+> printFormula frm
   Negation frm _ -> notDoc <+> printFormula frm
   Conjunction xs _ -> PBasic.sepByArbitrary andDoc $ 
                        map printFormula xs
   Disjunction xs _ -> PBasic.sepByArbitrary orDoc $ 
                         map printFormula xs
   Implication x y _ -> printFormula x <+> 
                          implies <+> printFormula y
   Equivalence x y _ -> printFormula x <+> 
                          equiv <+> printFormula y


printNomItem :: NOM_ITEM -> Doc
printNomItem (Nom_item xs _) =
  keyword (nomS ++ case xs of
     [_] -> ""
     _ -> "s") <+> ppWithCommas xs

-- TODO: this should be made more generic
printBasicSpec :: BASIC_SPEC -> Doc
printBasicSpec (Basic_spec xs) = vcat $ map pretty xs

printBasicItems :: BASIC_ITEMS -> Doc
printBasicItems (Axiom_items xs) = vcat $ map (addBullet . pretty) xs
printBasicItems (Pred_decl x) = pretty x
printBasicItems (Nom_decl x) = pretty x

{-
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
-}

