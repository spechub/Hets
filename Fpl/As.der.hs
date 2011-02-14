{- |
Module      :  $Header$
Description :  abstract syntax for FPL
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

abstract syntax for FPL, logic for functional programs
as CASL extension
-}

module Fpl.As where

-- DrIFT command
{-! global: GetRange !-}

import Common.AS_Annotation
import Common.DocUtils
import Common.Id

import CASL.AS_Basic_CASL

type FplBasicSpec = BASIC_SPEC FunDef FreeType TermExt

type FplTerm = TERM TermExt

data FreeType = FreeType [Annoted DATATYPE_DECL] Range
  deriving Show

instance Pretty FreeType

data FunDef = FunDef OP_NAME [VAR_DECL] SORT (Annoted FplTerm) Range
  deriving (Show, Eq, Ord)

instance Pretty FunDef

data TermExt =
    FixDef FunDef -- ^ formula
  | Case FplTerm [(FplTerm, FplTerm)] Range
  | Let FunDef FplTerm Range
  | IfThenElse FplTerm FplTerm FplTerm Range
  deriving (Show, Eq, Ord)

instance Pretty TermExt

