{- |
Module      :  $Header$
Description :  Abstract Maude Syntax
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

import Common.Id hiding (Id)
import Common.Doc (specBraces, text)
import Common.DocUtils (Pretty(..))

-- * Types

newtype MaudeText = MaudeText String deriving (Show)

instance Pretty MaudeText where
    pretty (MaudeText s) = specBraces $ text s

instance GetRange MaudeText

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

-- * Construction

-- | Create a 'Var' 'Term' from the given arguments.
mkVar :: String -> Type -> Term
mkVar = Var . mkSimpleId

-- * Information Extraction

-- | Extract the 'Type' from the given 'Term'.
getTermType :: Term -> Type
getTermType term = case term of
    Const _ typ   -> typ
    Var _ typ     -> typ
    Apply _ _ typ -> typ

-- * Attribute Classification

-- | True iff the argument is the @assoc@ attribute.
assoc :: Attr -> Bool
assoc attr = case attr of
    Assoc -> True
    _ -> False

-- | True iff the argument is the @comm@ attribute.
comm :: Attr -> Bool
comm attr = case attr of
    Comm -> True
    _ -> False

-- | True iff the argument is the @idem@ attribute.
idem :: Attr -> Bool
idem attr = case attr of
    Idem -> True
    _ -> False

-- | True iff the argument is the identity attribute.
idtty :: Attr -> Bool
idtty attr = case attr of
    Id _ -> True
    _ -> False

-- | True iff the argument is the left identity attribute.
leftId :: Attr -> Bool
leftId attr = case attr of
    LeftId _ -> True
    _ -> False

-- | True iff the argument is the right identity attribute.
rightId :: Attr -> Bool
rightId attr = case attr of
    RightId _ -> True
    _ -> False

-- | True iff the argument is the @ctor@ attribute.
ctor :: Attr -> Bool
ctor attr = case attr of
    Ctor -> True
    _ -> False

-- | True iff the argument is the @owise@ attribute.
owise :: StmntAttr -> Bool
owise attr = case attr of
    Owise -> True
    _ -> False
