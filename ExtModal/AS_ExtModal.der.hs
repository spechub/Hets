{- |
Module      :  $Header$
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher

Maintainer  :  codruta.liliana@gmail.com
Stability   :  experimental
Portability :  portable

-}

module ExtModal.AS_ExtModal where


import Common.Id
import Common.AS_Annotation
import CASL.AS_Basic_CASL

-- DrIFT command
{-! global: GetRange !-}

type EM_BASIC_SPEC = BASIC_SPEC EM_BASIC_ITEM EM_SIG_ITEM EM_FORMULA

type AnEModForm = Annoted (FORMULA EM_FORMULA)

data EM_BASIC_ITEM =
        Simple_mod_decl Bool [Annoted SIMPLE_ID] [AnEModForm] Range
        -- True if time modality, False if not
        | Nominal_decl [Annoted SIMPLE_ID] Range
        deriving Show

data MODALITY = Simple_modality SIMPLE_ID |
                Composition MODALITY MODALITY |
                Union MODALITY MODALITY |
                TransitiveClosure MODALITY |
                Guard (FORMULA EM_FORMULA)
        deriving (Eq, Ord, Show)

data RIGOR = Rigid | Flexible deriving Show

data EM_SIG_ITEM =
          Rigid_op_items RIGOR [Annoted (OP_ITEM EM_FORMULA)] Range
                 -- pos: op, semi colons
        | Rigid_pred_items RIGOR [Annoted (PRED_ITEM EM_FORMULA)] Range
                 -- pos: pred, semi colons
             deriving Show


data NOMINAL = Nominal SIMPLE_ID deriving (Show, Eq, Ord)

data EM_FORMULA
  = BoxOrDiamond Bool MODALITY Bool Int (FORMULA EM_FORMULA) Range
    -- The first identifier and the term specify the kind of the modality
    -- pos: "[]" or  "<>", True if Box, False if Diamond;
    -- The second identifier is used for grading:
    -- pos: "<=" or ">=", True if Leq (less than/equal),
    -- False if Geq (greater than/equal), positive integers
  | Hybrid Bool NOMINAL (FORMULA EM_FORMULA) Range
                -- True if @, False if Here
                -- pos: "@", "Here"
  | UntilSince Bool (FORMULA EM_FORMULA) (FORMULA EM_FORMULA) Range
                -- pos: "Until", "Since", True if  Until, False if Since
  | PathQuantification  Bool (FORMULA EM_FORMULA) Range
    -- pos: "A", "E", True if Universal (A), False if Existential (E)
  | NextY Bool (FORMULA EM_FORMULA) Range
                -- pos: "X", "Y", True if Next (X), False if Yesterday (Y)
  | StateQuantification Bool Bool (FORMULA EM_FORMULA) Range
    -- The time direction (past vs future) and
    -- quantification type must be given, as follows:
                -- (True, True) if (Future, Universal), i.e. Generally (G);
                -- (True, False) if (Future, Existential), i.e. Eventually (F);
                -- (False, True) if (Past, Universal), i.e. Hitherto (H);
                -- (False, False) if (Past, Existential), i.e. Previously (P);
                -- pos: "G", "H", "F", "P"
  | FixedPoint Bool VAR (FORMULA EM_FORMULA) Range
                -- pos: "mu", "nu", True if "mu", False if "nu"
    deriving (Eq, Ord, Show)
