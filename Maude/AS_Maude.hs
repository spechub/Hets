{-
  Ref.
  http://maude.cs.uiuc.edu/
-}

module Maude.AS_Maude where
  
import qualified Common.Id as Id
  
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
          | Gather [Id.Token]
          | Format [Id.Token]
          | Ctor
          | Config
          | Object
          | Msg
          | Frozen [Int]
          | Poly [Int]
          deriving (Show, Read)

data StmntAttr = Label Id.Token
               | Metadata String
               | Owise
               | Nonexec
               | Print [Id.Token]
               deriving (Show, Read)

data Term = Const Id.Token Type
          | Var Id.Token Type
          | Apply Id.Token [Term]
          deriving (Show, Read)

data Type = TypeSort Sort
          | TypeKind Kind
          deriving (Show, Read)

newtype Sort = SortId Id.Token
             deriving (Show, Read)

newtype Kind = KindId Id.Token
             deriving (Show, Read)

newtype ParamId = ParamId Id.Token
                deriving (Show, Read)

newtype ModId = ModId Id.Token
              deriving (Show, Read)

newtype LabelId = LabelId Id.Token
                deriving (Show, Read)

newtype OpId = OpId Id.Token
             deriving (Show, Read)