{-# OPTIONS -XDeriveDataTypeable #-}
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

import Common.ATerm.Lib
import Common.Doc
import Common.DocUtils
import Common.Id
import Data.Typeable

data Spec = Spec ModId [Parameter] [Statement]
          deriving (Show, Read)

data Theory = Theory ModId [Statement]
            deriving (Show, Read)

data Parameter = Parameter Sort ModExp
               deriving (Show, Read)

data ModExp = ModExp ModId
            | ParenthesesModExp ModExp
            | SummationModExp ModExp ModExp
            | RenamingModExp ModExp [Renaming]
            deriving (Show, Read)

data Renaming = SortRenaming Sort Sort
              | LabelRenaming LabelId LabelId
              | OpRenaming1 OpId ToPartRenaming
              | OpRenaming2 OpId [Type] Type ToPartRenaming
              deriving (Show, Read)

newtype MaudeText = MaudeText String deriving (Show, Typeable)

instance Pretty MaudeText where
  pretty (MaudeText s) = text s

instance ShATermConvertible MaudeText where
  toShATermAux att0 (MaudeText a) = do
        (att1, a') <- toShATerm' att0 a
        return $ addATerm (ShAAppl "MaudeText" [a'] []) att1
  fromShATermAux ix att0 =
        case getShATerm ix att0 of
            ShAAppl "MaudeText" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, MaudeText a') }
            u -> fromShATermError "MaudeText" u

data Statement = ImportStmnt Import
               | SortStmnt Sort
               | SubsortStmnt SubsortDecl
               | OpStmnt Operator
               | MbStmnt Membership
               | EqStmnt Equation
               | RlStmnt Rule
               deriving (Show, Read)

data Import = Including ModExp
            | Extending ModExp
            | Protecting ModExp
            deriving (Show, Read)

data SubsortDecl = Subsort Sort Sort
                 deriving (Show, Read)

data Operator = Op OpId [Type] Type [Attr]
              deriving (Show, Read)

data Equation = Eq Term Term [EqCondition] [StmntAttr]
              deriving (Show, Read)

data Membership = Mb Term Sort [EqCondition] [StmntAttr]
                deriving (Show, Read)

data Rule = Rl Term Term [Condition] [StmntAttr]
          deriving (Show, Read)

data EqCondition = EqCond Term Term
                 | MbCond Term Sort
                 | MatchCond Term Term
                 deriving (Show, Read)

data Condition = EqCondition
               | RwCond Term Term
               deriving (Show, Read)

data ToPartRenaming = To OpId [Attr]
                    deriving (Show, Read)

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
          | Gather [Token]
          | Format [Token]
          | Ctor
          | Config
          | Object
          | Msg
          | Frozen [Int]
          | Poly [Int]
          deriving (Show, Read)

data StmntAttr = Label Token
               | Metadata String
               | Owise
               | Nonexec
               | Print [Token]
               deriving (Show, Read)

data Term = Const Token Type
          | Var Token Type
          | Apply Token [Term]
          deriving (Show, Read)

data Type = TypeSort Sort
          | TypeKind Kind
          deriving (Show, Read)

newtype Sort = SortId Token
             deriving (Show, Read)

newtype Kind = KindId Token
             deriving (Show, Read)

newtype ParamId = ParamId Token
                deriving (Show, Read)

newtype ModId = ModId Token
              deriving (Show, Read)

newtype LabelId = LabelId Token
                deriving (Show, Read)

newtype OpId = OpId Token
             deriving (Show, Read)
