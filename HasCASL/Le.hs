
{- HetCATS/HasCASL/Le.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   abstract syntax after/during static analysis
-}

module Le where

import Id
import Set
import FiniteMap

type TypeId = Id

-- "*", "->", etc. are predefined type constructors
-- the unit type is the empty product

-----------------------------------------------------------------------------
-- Kinds
-----------------------------------------------------------------------------

data Kind  = Star ExtClass | Kfun Kind Kind

instance Eq Kind where
    Star _ == Star _ = True
    Kfun f1 a1 == Kfun f2 a2 = f1 == f2 && a1 == a2
    _ == _ = False

instance Ord Kind where
    Star _ <= Star _ = True
    Kfun f1 a1 <= Kfun f2 a2 = if f1 <= f2 then 
			       if f2 <= f1 then a1 <= a2
				  else True
			       else False
    Star _ <= Kfun _ _ = True
    Kfun _ _ <= Star _ = False

type ClassId = Id

data Class = Universe 
	   | ClassName ClassId
	   | Intersection (Set ClassId)

data Variance = CoVar | ContraVar | InVar 

data ExtClass = ExtClass Class Variance

star :: Kind
star = Star $ ExtClass Universe InVar

type ClassInst    = ([Id], [Inst]) -- super classes and instances
type Inst     = Qual Pred

-----------------------------------------------------------------------------

type ClassEnv = FiniteMap Id ClassInst

super     :: ClassEnv -> Id -> [Id]
super ce i = case lookupFM ce i of Just (is, _) -> is
				   Nothing -> []

insts     :: ClassEnv -> Id -> [Inst]
insts ce i = case lookupFM ce i of Just (_, its) -> its
				   Nothing -> []

-----------------------------------------------------------------------------
-- Types
-----------------------------------------------------------------------------

data Tyvar = Tyvar { typeVarId :: TypeId, typeKind :: Kind } deriving (Eq, Ord)

data Tycon = Tycon TypeId Kind
             deriving Eq

data Type  = TVar Tyvar | TCon Tycon | TAp  Type Type | TGen Int
             deriving Eq

data Pred   = IsIn Id Type
              deriving Eq

data Qual t = [Pred] :=> t
              deriving Eq

data Scheme = Scheme [Kind] (Qual Type)
              deriving Eq

type Assumps = FiniteMap Id [Scheme]

-----------------------------------------------------------------------------
-- Symbols
-----------------------------------------------------------------------------

data SymbType = OpType Scheme
	      | TypeKind Kind
	      | Class

data Symbol = Symbol {symbId :: Id, sumbType :: SymbType}
-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symbol] 

-----------------------------------------------------------------------------
-- Items
-----------------------------------------------------------------------------

data GenKind = Free | Generated | Loose deriving (Show,Eq)      

data VarDecl = VarDecl { varId :: Id, varType :: Type }

data TypeBody = Alias Type -- non-recursive
	      | Datatype [Alternative] GenKind GenItems
	      | SubtypeDefn VarDecl Type Term -- a formula

-- type variables correspond to the kind
data TypeDefn = TypeDefn [Tyvar] TypeBody

-- full function type of constructor (result sort is the data type)
data Alternative = Construct Id Type [Component] 
		 | Subtype Type

-- full function type of a selector (result sort is component sort)
data Component = Component (Maybe Id) Type 

data ClassItem = ClassItem { classId :: Id
			   , subClasses :: [ClassId]
			   , superClasses :: [ClassId]
			   , classDefn :: Maybe Class 
                           , classBody :: [SigItem]
			   }

data TypeRel = TypeRel [Tyvar] Type Type

data TypeItem = TypeItem{ typeConstrId :: Id
			, itemKind :: Kind
			, subtypes :: [TypeRel]
			, supertypes :: [TypeRel]
			, typeDefn :: Maybe TypeDefn
			}

type ConsId = Symbol
type SelId = Symbol

data OpDefn = OpDef [VarDecl] Term
            | Constr ConsId
            | Select [ConsId] SelId

data BinOpAttr = Assoc | Comm | Idem deriving (Show) 

data OpAttr = BinOpAttr BinOpAttr | UnitOpAttr Term

data OpItem = OpItem { opId :: Id
		     , opType :: Scheme
		     , opAttrs :: [OpAttr]
		     , opDefn :: Maybe OpDefn
		     }		      

data TypeOp = OfType | AsType | InType deriving (Eq)     

data Binder = LambdaTotal | LambdaPartial
	    | Forall 
            | Exists | ExistsUnique 
	    deriving (Eq)

data Term = BaseName Id Scheme [Type]  -- instance
	  | VarId Id Type Class
          | Application Term Term 
	  | Binding Binder [VarDecl] Term
	  | Typed Term TypeOp Type

data SigItem = AClassItem ClassItem
	     | ATypeItem TypeItem
	     | AnOpItem OpItem
