{- |
Module      :  $Header$
Copyright   :  DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

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
        ModDecl Bool Bool [Annoted Id] [AnEModForm] Range
        -- Booleans: time (True) or not and term (True) or simple modality
        | Nominal_decl [Annoted SIMPLE_ID] Range
        deriving Show

data ModOp = Composition | Intersection | Union deriving (Eq, Ord)

instance Show ModOp where
  show o = case o of
    Composition -> ";"
    Intersection -> "&"
    Union -> "|"

data MODALITY =
    SimpleMod SIMPLE_ID
  | TermMod (TERM EM_FORMULA)
  | ModOp ModOp MODALITY MODALITY
  | TransClos MODALITY
  | Guard (FORMULA EM_FORMULA)
        deriving (Eq, Ord, Show)

-- True booleans for rigid items, False for flexible ones
data EM_SIG_ITEM =
          Rigid_op_items Bool [Annoted (OP_ITEM EM_FORMULA)] Range
                 -- pos: op, semi colons
        | Rigid_pred_items Bool [Annoted (PRED_ITEM EM_FORMULA)] Range
                 -- pos: pred, semi colons
             deriving Show

data EM_FORMULA
  = BoxOrDiamond Bool MODALITY Bool Int (FORMULA EM_FORMULA) Range
    {- The first identifier and the term specify the kind of the modality
    pos: "[]" or  "<>", True if Box, False if Diamond;
    The second identifier is used for grading:
    pos: "<=" or ">=", True if Leq (less than/equal),
    False if Geq (greater than/equal), positive integers -}
  | Hybrid Bool SIMPLE_ID (FORMULA EM_FORMULA) Range
                {- True if @, False if Here
                pos: "@", "Here" -}
  | UntilSince Bool (FORMULA EM_FORMULA) (FORMULA EM_FORMULA) Range
                -- pos: "Until", "Since", True if  Until, False if Since
  | PathQuantification Bool (FORMULA EM_FORMULA) Range
    -- pos: "A", "E", True if Universal (A), False if Existential (E)
  | NextY Bool (FORMULA EM_FORMULA) Range
                -- pos: "X", "Y", True if Next (X), False if Yesterday (Y)
  | StateQuantification Bool Bool (FORMULA EM_FORMULA) Range
    {- The time direction (past vs future) and
    quantification type must be given, as follows:
                (True, True) if (Future, Universal), i.e. Generally (G);
                (True, False) if (Future, Existential), i.e. Eventually (F);
                (False, True) if (Past, Universal), i.e. Hitherto (H);
                (False, False) if (Past, Existential), i.e. Previously (P);
                pos: "G", "H", "F", "P" -}
  | FixedPoint Bool VAR (FORMULA EM_FORMULA) Range
                -- pos: "mu", "nu", True if "mu", False if "nu"
    deriving (Eq, Ord, Show)
