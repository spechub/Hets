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

data FrameForm = FrameForm
  { frameVars :: [VAR_DECL]
  , frameForms :: [Annoted (FORMULA EM_FORMULA)]
  , frameFormRange :: Range
  } deriving (Show, Eq, Ord)

data ModDefn = ModDefn Bool Bool [Annoted Id] [FrameForm] Range
        -- Booleans: time (True) or not and term (True) or simple modality
    deriving (Show, Eq, Ord)

data EM_BASIC_ITEM =
        ModItem ModDefn
        | Nominal_decl [Annoted SIMPLE_ID] Range
        deriving Show

data ModOp = Composition | Intersection | Union deriving (Eq, Ord)

{- Union corresponds to alternative and intersection to parallel composition.
The symbols used (like for logical "and" and "or") may be confusing!
Guarded alternatives may be used to simulate if-then-else.
-}

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

{-
Note, that a diamond formula "<m> f" stand for "<m>1 f" or "<m> >=1 f"
Generally "<m>n f" or "<m> >=n f" (n positive) means, that there are at least n
successor worlds (wrt m) in which f holds. (This is called grading.)

"<m> <=n f" is rarely used (there are at most n successor worlds that fulfill f)

By definition "[m]n f" is "not <m>n not f" and thus means: f holds in all
successor worlds except in at most n-1 successor worlds.
A notation like "[m]<n f" or "[m]<=0 f" would be illegal
(only <= or >= with positive n is allowed),
thus here "[m]n f" stands for "[m]>=n f" and "[m]<=n f" for "not <m> <=n not f"

Another interpretation of "[m]n f" is that any subset with n successor worlds
contains at least one successor world fulfilling f.

"<m> <=n f" seems to identical "[m]>=n+1 not f"
(at most n successor worlds fulfill f)

By duality: [m]<=n f <=> not <m> <=n not f <=> not [m]>=n+1 f
and: "<m> <=n f" <=> [m]>=n+1 not f <=> not <m> >=n+1 f
thus: <m> >=n f <=> not <m> <=n-1 f <=> [m]<=n-1 not f
and: [m]>=n f <=> not [m] <=n-1 f

There are exactly n successor worlds can be expressed as:
<m> >=n f /\ <m> <=n f
or: <m> >=n f /\ not <m> >=n+1 f
or: [m]>=n+1 not f /\ [m]<=n-1 not f

Also box formulas using n (> 1) are rarely used!
-}

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
  | ModForm ModDefn
    deriving (Eq, Ord, Show)
