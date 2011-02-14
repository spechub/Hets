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
import Common.Doc
import Common.DocUtils
import Common.Id

import CASL.AS_Basic_CASL
import CASL.ToDoc

type FplBasicSpec = BASIC_SPEC FunDef FreeType TermExt

type FplTerm = TERM TermExt

data FreeType = FreeType [Annoted DATATYPE_DECL] Range
  deriving Show

printDD :: DATATYPE_DECL -> Doc
printDD (Datatype_decl s as _) =
    sep [pretty s <+> keyword "free" <+> keyword "with"
        , sep $ prepPunctuate (bar <> space)
          $ map (printAnnoted printALTERNATIVE) as ]

instance Pretty FreeType where
  pretty (FreeType ds _) =
    keyword "sort" <+> semiAnnos printDD ds

data FunDef = FunDef OP_NAME [VAR_DECL] SORT (Annoted FplTerm) Range
  deriving (Show, Eq, Ord)

instance Pretty FunDef where
  pretty (FunDef n vs s t _) =
    fsep [keyword "fun" <+> pretty n <>
          (if null vs then empty else parens (printVarDecls vs))
          <+> colon <+> pretty s
         , equals <+> printAnnoted pretty t]

data TermExt =
    FixDef FunDef -- ^ formula
  | Case FplTerm [(FplTerm, FplTerm)] Range
  | Let FunDef FplTerm Range
  | IfThenElse FplTerm FplTerm FplTerm Range
  deriving (Show, Eq, Ord)

instance Pretty TermExt where
  pretty t = case t of
    FixDef fd -> pretty fd
    Case c l _ ->
      sep $ (keyword "case" <+> pretty c <+> keyword "of")
          : prepPunctuate (bar <> space)
            (map (\ (p, e) -> fsep [pretty p, implies, pretty e]) l)
    Let fd i _ -> sep [keyword "let" <+> pretty fd <+> keyword "in", pretty i]
    IfThenElse i d e _ ->
        fsep [ keyword "if" <+> pretty i
             , keyword "then" <+> pretty d
             , keyword "else" <+> pretty e ]
