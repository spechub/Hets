module LocalEnv where

-- $Header$

import Id
import AS_Annotation
import FiniteMap
import Graph
import List(intersperse)

type SortId = Id  -- non-mixfix, but possibly compound

data FunKind = Total | Partial deriving (Eq, Ord)

-- constants have empty argument lists 
data OpType = OpType {opKind :: FunKind, opArgs :: [SortId], opRes :: SortId} 
	      deriving (Eq, Ord)

type PredType = [SortId]

data SymbType = OpAsItemType OpType
	      | PredType PredType
	      | Sort 
		deriving (Eq, Ord)

data Symbol = Symbol {symbId :: Id, symbType :: SymbType} deriving (Eq, Ord)

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symbol] 

-- full function type of a selector (result sort is component sort)
data Component = Component (Maybe Id) OpType [Pos]

-- full function type of constructor (result sort is the data type)
data Alternative = Construct Id OpType [Component] [Pos] 
		 | Subsort SortId [Pos]

-- looseness of a datatype
-- a datatype may (only) be (sub-)part of a "sort-gen"
data GenKind = Free | Generated | Loose deriving (Show,Eq)      

data VarDecl = VarDecl {varId :: Id, varSort :: SortId}

-- sort defined as predicate subtype or as more or less loose datatype
data SortDefn = SubsortDefn VarDecl Formula [Pos]
              | Datatype [Annoted Alternative] GenKind GenItems [Pos]

-- the sub- and supertypes of a sort 
data SortRels = SortRels { subsorts :: [SortId]  -- explicitly given
			 , supersorts :: [SortId] 
			 , allsubsrts :: [SortId] -- transitively closed 
			 , allsupersrts :: [SortId]
			 } 

data ItemStart = Key | Comma | Semi | Less

data ItemPos = ItemPos String ItemStart [Pos] 
-- "filename" plus positions of op, :, * ... *, ->, ",", assoc ... 

-- sort or type 
data SortItem = SortItem { sortId :: SortId
			 , sortRels :: SortRels
                         , sortDef  :: Maybe SortDefn
                         , sortPos :: ItemPos
                         , altSorts :: [ItemPos] -- alternative positions
			 }                       -- of repeated decls

data BinOpAttr = Assoc | Comm | Idem deriving (Show) 

data OpAttr = BinOpAttr BinOpAttr | UnitOpAttr Term

type ConsId = Symbol
type SelId = Symbol

data OpDefn = OpDef [VarDecl] (Annoted Term) [[Pos]] -- ,,,;,,,;,,,
            | Constr ConsId          -- inferred
            | Select [ConsId] SelId  -- inferred

data OpItem = OpItem { opId :: Id
		     , opType :: OpType
		     , opAttrs :: [OpAttr]
		     , opDefn :: Maybe OpDefn
                     , opPos :: ItemPos      -- positions of merged attributes
		     , altOps :: [ItemPos]   -- may get lost
		     }

data PredDefn = PredDef [VarDecl] Formula [[Pos]]

data PredItem = PredItem { predId :: Id
			 , predType :: PredType
			 , predDefn :: Maybe PredDefn
			 , predPos :: ItemPos    
			 , altPreds :: [ItemPos] 
			 }

data TypeQualifier = OfType | AsType

data Qualified = Explicit | Inferred

-- a constant op has an empty list of Arguments
data Term = VarId Id SortId Qualified [Pos]
	  | OpAppl Id OpType [Term] Qualified [Pos]  
	  | Typed Term TypeQualifier SortId [Pos]
          | Cond Term Formula Term [Pos]

data Quantifier =  Forall | Exists | ExistsUnique

data LogOp = NotOp | AndOp | OrOp | ImplOp | EquivOp | IfOp 

data PolyOp = DefOp | EqualOp | ExEqualOp

data Formula = Quantified Quantifier [VarDecl] Formula [[Pos]]
	     | Connect LogOp [Formula] [Pos]
	     | TermTest PolyOp [Term] [Pos]
	     | PredAppl Id PredType [Term] Qualified [Pos]  
	     | ElemTest Term SortId [Pos]
	     | FalseAtom [Pos]
	     | TrueAtom [Pos]
	     | AnnFormula (Annoted Formula)

data SigItem = ASortItem (Annoted SortItem)
	     | AnOpItem (Annoted OpItem)
	     | APredItem (Annoted PredItem)

-- lost are unused global vars
-- and annotations for several ITEMS 

data Sign = SignAsList [SigItem]

data LocalEnv = SignAsMap (FiniteMap Id [SigItem]) (Graph SortId ())

data RaySymbol = ASymbol Symbol | AnID Id | AKindedId Kind Id
data Kind = SortKind | FunKind | PredKind

data Axiom = AxiomDecl [VarDecl] Formula [[Pos]] -- ,,,;,,,;

data Sentence = Axiom (Annoted Axiom) 
	      | GenItems GenItems [Pos] -- generate/free, { , }

getLabel :: Sentence -> String
getLabel (Axiom ax) = let annos = r_annos(ax)
                          isLabel a = case a of Label _ _ -> True; _ -> False 
                          labels = filter isLabel annos
		          getLabel(Label l _) = concat l  		    
                      in if null labels then "" else getLabel(head(labels))
getLabel (GenItems l _) = let srts = filter (\x ->
					     case x of Symbol _ Sort -> True;
                                                       _ -> False) l
                          in "ga_generated_" ++ concat 
				 (intersperse "__" 
				      (map (show . symbId) srts))
