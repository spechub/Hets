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

import Common.Doc (specBraces, text)
import Common.DocUtils (Pretty(..))
import Common.Id (Token)

type Qid = Token

data Spec = SpecMod Module
          | SpecTh Module
          | SpecView View
          deriving (Show, Read, Ord, Eq)

data Module = Module ModId [Parameter] [Statement]
            deriving (Show, Read, Ord, Eq)

data View = View ModId ModExp ModExp [Renaming]
            deriving (Show, Read, Ord, Eq)

data Parameter = Parameter Sort ModExp
               deriving (Show, Read, Ord, Eq)

data ModExp = ModExp ModId
            | SummationModExp ModExp ModExp
            | RenamingModExp ModExp [Renaming]
            | InstantiationModExp ModExp [ViewId]
            deriving (Show, Read, Ord, Eq)

data Renaming = SortRenaming Sort Sort
              | LabelRenaming LabelId LabelId
              | OpRenaming1 OpId ToPartRenaming
              | OpRenaming2 OpId [Type] Type ToPartRenaming
              | TermMap Term Term
              deriving (Show, Read, Ord, Eq)

data ToPartRenaming = To OpId [Attr]
                    deriving (Show, Read, Ord, Eq)

newtype MaudeText = MaudeText String deriving (Show)

instance Pretty MaudeText where
  pretty (MaudeText s) = specBraces $ text s

data Statement = ImportStmnt Import
               | SortStmnt Sort
               | SubsortStmnt SubsortDecl
               | OpStmnt Operator
               | EqStmnt Equation
               | MbStmnt Membership
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

data Membership = Mb Term Sort [Condition] [StmntAttr]
                deriving (Show, Read, Ord, Eq)

data Equation = Eq Term Term [Condition] [StmntAttr]
              deriving (Show, Read, Ord, Eq)

data Rule = Rl Term Term [Condition] [StmntAttr]
          deriving (Show, Read, Ord, Eq)

data Condition = EqCond Term Term
               | MbCond Term Sort
               | MatchCond Term Term
               | RwCond Term Term
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
          | Special [Hook]
          deriving (Show, Read, Ord, Eq)

data StmntAttr = Label Qid
               | Metadata String
               | Owise
               | Nonexec
               | Print [Qid]
               deriving (Show, Read, Ord, Eq)

data Hook = IdHook Qid [Qid]
          | OpHook Qid Qid [Qid] Qid
          | TermHook Qid Term
          deriving (Show, Read, Ord, Eq)

data Term = Const Qid Type
          | Var Qid Type
          | Apply Qid [Term] Type
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

newtype ViewId = ViewId Qid
                deriving (Show, Read, Ord, Eq)

newtype ModId = ModId Qid
              deriving (Show, Read, Ord, Eq)

newtype LabelId = LabelId Qid
                deriving (Show, Read, Ord, Eq)

newtype OpId = OpId Qid
             deriving (Show, Read, Ord, Eq)

-- | Auxiliary function to extract the type of a term
getTermType :: Term -> Type
getTermType (Const _ ty) = ty
getTermType (Var _ ty) = ty
getTermType (Apply _ _ ty) = ty

-- | Auxiliary functions to traverse the attributes

-- | check if a list of attributes contains the assoc attribute
assoc :: Attr -> Bool
assoc a = case a of
       Assoc -> True
       _ -> False

-- | check if a list of attributes contains the comm attribute
comm :: Attr -> Bool
comm a = case a of
       Comm -> True
       _ -> False

-- | check if a list of attributes contains the idem attribute
idem :: Attr -> Bool
idem a = case a of
       Idem -> True
       _ -> False

-- | check if a list of attributes contains the identity attribute
idtty :: Attr -> Bool
idtty a = case a of
       Id _ -> True
       _ -> False

-- | check if a list of attributes contains the left identity attribute
leftId :: Attr -> Bool
leftId a = case a of
       LeftId _ -> True
       _ -> False

-- | check if a list of attributes contains the right identity attribute
rightId :: Attr -> Bool
rightId a = case a of
       RightId _ -> True
       _ -> False

-- | check if a list of attributes contains the right identity attribute
ctor :: Attr -> Bool
ctor a = case a of
       Ctor -> True
       _ -> False

-- | check if a list of attributes contains the owise attribute
owise :: StmntAttr -> Bool
owise a = case a of
       Owise -> True
       _ -> False

-- | returns the identity term from the attribute set
getIdentity ::  [Attr] -> Maybe Term
getIdentity [] = Nothing
getIdentity (a : as) = case a of
       Id t -> Just t
       RightId t -> Just t
       LeftId t -> Just t
       _ -> getIdentity as
