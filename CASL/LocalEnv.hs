module LocalEnv where

import Id
import AS_Annotation
import Set
import FiniteMap

type Anno = Annotation

type SortId = Id -- or SIMPLE_ID

-- the sub- and supertypes of a sort 
data SortRels = SortRels { subsorts :: [SortId], supersorts :: [SortId] } 

data FunKind = Total | Partial deriving (Eq, Ord)

-- constants have empty argument lists 
data OpType = OpType {opKind :: FunKind, opArgs :: [SortId], opRes :: SortId} 
	      deriving (Eq, Ord)

data ItemType = OpAsItemType OpType
	      | PredType [SortId]
	      | Sort 
		deriving (Eq, Ord)

data ItemId = ItemId {itemId :: Id, itemType :: ItemType} deriving (Eq, Ord)

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [ItemId] 

-- full function type of a selector (result sort is component sort)
data Component = Component (Maybe Id) OpType 

-- full function type of constructor (result sort is the data type)
data Alternative = Construct Id OpType [Component] 
		 | Subsort SortId

-- looseness of a datatype
-- a datatype may (only) be (sub-)part of a "sort-gen"
data GenKind = Free | Generated | Loose deriving (Show,Eq)      

data VarDecl = VarDecl {varId :: Id, varSort :: SortId}

-- sort defined as predicate subtype or as more or less loose datatype
data SortDefn = SubsortDefn VarDecl SortId Formula
              | Datatype [Alternative] GenKind GenItems

-- sort or type 
data SortItem = SortItem { sortId :: SortId
			 , sortRels :: SortRels
                         , sortDef  :: Maybe SortDefn
			 , sortAn   :: [Anno]
			 }

data BinOpAttr = Assoc | Comm | Idem deriving (Show) 

data OpAttr = BinOpAttr BinOpAttr | UnitOpAttr Term

type ConsId = ItemId
type SelId = ItemId

data OpDefn = OpDef [VarDecl] Term
            | Constr ConsId
            | Select [ConsId] SelId

data OpItem = OpItem { opId :: Id
		     , opType :: OpType
		     , opAttrs :: [OpAttr]
		     , opDefn :: Maybe OpDefn
		     , opAn :: [Anno]
		     }

data PredDefn = PredDef [VarDecl] Formula

data PredItem = PredItem { predId :: Id
			 , predType :: [SortId]
			 , predDefn :: Maybe PredDefn
			 , predAn :: [Anno]
			 }

data TypeOp = OfType | AsType

-- a constant op has an empty list of Arguments
data Term = Literal Token SortId
	  | VarId Id SortId
	  | OpAppl Id OpType [Term] 
	  | Typed Term TypeOp SortId
          | Cond Term Formula Term

data Binder =  Forall | Exists | ExistsUnique

data LogOp = NotOp | AndOp | OrOp | ImplOp | EquivOp | IfOp 

data PolyOp = DefOp | EqualOp | ExEqualOp

-- true and false are constant predicates (Id)
data Formula = Binding Binder [VarDecl] Formula
	     | Connect LogOp [Formula]
	     | TermTest PolyOp [Term]
	     | PredAppl Id [SortId] [Term]
	     | ElemTest Term SortId

data SigItem = ASortItem SortItem 
	     | AnOpItem OpItem
	     | APredItem OpItem


type IdMap a = FiniteMap Id a

type OpMap = IdMap (FiniteMap OpType OpItem)
type PredMap = IdMap (FiniteMap [SortId] PredItem) 

data Sign = SignAsList [SigItem]
	  | SignAsMap (FiniteMap ItemId SigItem)
          | SignForSearch { sorts :: Set SortId
			  , ops :: OpMap 
			  , preds :: PredMap} 

data Axiom = AxiomDecl [VarDecl] Formula [Anno]

data Sentence = Axiom Axiom | GenItems GenItems


