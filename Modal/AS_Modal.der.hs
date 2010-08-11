{- |
Module      :  $Header$
Copyright   :  (c) T.Mossakowski, W.Herding, C.Maeder, Uni Bremen 2004-2006
License     :  GPLv2 or higher

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Abstract syntax for modal logic extension of CASL
  Only the added syntax is specified
-}

module Modal.AS_Modal where

import Common.Id
import Common.AS_Annotation
import CASL.AS_Basic_CASL

-- DrIFT command
{-! global: GetRange !-}

type M_BASIC_SPEC = BASIC_SPEC M_BASIC_ITEM M_SIG_ITEM M_FORMULA

type AnModFORM = Annoted (FORMULA M_FORMULA)

data M_BASIC_ITEM = Simple_mod_decl [Annoted SIMPLE_ID] [AnModFORM] Range
                  | Term_mod_decl [Annoted SORT] [AnModFORM] Range
                    deriving Show

data RIGOR = Rigid | Flexible deriving Show

data M_SIG_ITEM =
          Rigid_op_items RIGOR [Annoted (OP_ITEM M_FORMULA)] Range
                 -- pos: op, semi colons
        | Rigid_pred_items RIGOR [Annoted (PRED_ITEM M_FORMULA)] Range
                 -- pos: pred, semi colons
             deriving Show

data MODALITY = Simple_mod SIMPLE_ID | Term_mod (TERM M_FORMULA)
             deriving (Eq, Ord, Show)

data M_FORMULA = BoxOrDiamond Bool MODALITY (FORMULA M_FORMULA) Range
               -- The identifier and the term specify the kind of the modality
               -- pos: "[]" or  "<>", True if Box, False if Diamond
             deriving (Eq, Ord, Show)
