{- |
Module      :  $Header$
Description :  abstract maude syntax
Copyright   :  (c) DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  portable

The abstract syntax of maude. Basic specs are a list of statements excluding
imports. Sentences are equations, membership axioms, and rules. Sort, subsort
and operations should be converted to signature.

Because maude parses and typechecks an input string in one go, basic specs for
the logic instance are just a wrapped string that is created by a simple
parser.
-}

module Maude.AS_Maude where

import Common.Doc
import Common.DocUtils
import Common.Id (Token)

type Qid = Token

data Spec = SpecMod Module
          deriving (Show, Read, Ord, Eq)
--          | SpecView View

data Module = Module ModId [Parameter] [Statement]
            deriving (Show, Read, Ord, Eq)

data Parameter = Parameter Sort ModExp
               deriving (Show, Read, Ord, Eq)

data ModExp = ModExp ModId
            | ParenthesesModExp ModExp
            | SummationModExp ModExp ModExp
            | RenamingModExp ModExp [Renaming]
            deriving (Show, Read, Ord, Eq)

data Renaming = SortRenaming Sort Sort
              | LabelRenaming LabelId LabelId
              | OpRenaming1 OpId ToPartRenaming
              | OpRenaming2 OpId [Type] Type ToPartRenaming
              deriving (Show, Read, Ord, Eq)

newtype MaudeText = MaudeText String deriving (Show)

instance Pretty MaudeText where
  pretty (MaudeText s) = specBraces $ text s

data Statement = ImportStmnt Import
               | SortStmnt Sort
               | SubsortStmnt SubsortDecl
               | OpStmnt Operator
               | MbStmnt Membership
               | EqStmnt Equation
               | RlStmnt Rule
               deriving (Show, Read, Ord, Eq)

data Import = Including ModExp
            | Extending ModExp
            | Protecting ModExp
            deriving (Show, Read, Ord, Eq)

data SubsortDecl = Subsort Sort Sort
                 deriving (Show, Read, Ord, Eq)

data Operator = Op OpId [Type] Type [Attr]
              deriving (Show, Read, Ord, Eq)

data Equation = Eq Term Term [Condition] [StmntAttr]
              deriving (Show, Read, Ord, Eq)

data Membership = Mb Term Sort [Condition] [StmntAttr]
                deriving (Show, Read, Ord, Eq)

data Rule = Rl Term Term [Condition] [StmntAttr]
          deriving (Show, Read, Ord, Eq)

data Condition = EqCond Term Term
               | MbCond Term Sort
               | MatchCond Term Term
               | RwCond Term Term
               deriving (Show, Read, Ord, Eq)

data ToPartRenaming = To OpId [Attr]
                    deriving (Show, Read, Ord, Eq)

data Attr = Assoc
          | Comm
          | Idem
          | Iter
          | Id Term
          | LeftId Term
          | RightId Term
          | Strat [Int]
          | Memo
          | Prec Int
          | Gather [Qid]
          | Format [Qid]
          | Ctor
          | Config
          | Object
          | Msg
          | Frozen [Int]
          | Poly [Int]
          | Special
          deriving (Show, Read, Ord, Eq)

data StmntAttr = Label Qid
               | Metadata String
               | Owise
               | Nonexec
               | Print [Qid]
               deriving (Show, Read, Ord, Eq)

data Term = Const Qid Type
          | Var Qid Type
          | Apply Qid [Term]
          deriving (Show, Read, Ord, Eq)

data Type = TypeSort Sort
          | TypeKind Kind
          deriving (Show, Read, Ord, Eq)

newtype Sort = SortId Qid
             deriving (Show, Read, Ord, Eq)

newtype Kind = KindId Qid
             deriving (Show, Read, Ord, Eq)

newtype ParamId = ParamId Qid
                deriving (Show, Read, Ord, Eq)

newtype ModId = ModId Qid
              deriving (Show, Read, Ord, Eq)

newtype LabelId = LabelId Qid
                deriving (Show, Read, Ord, Eq)

newtype OpId = OpId Qid
             deriving (Show, Read, Ord, Eq)
