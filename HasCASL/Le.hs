module Le where

import Id
import Set

type TypeId = Id

-- "*", "->", etc. are predefined type constructors
-- the unit type is the empty product
data Type = Type { typeId :: TypeId, typeArgs :: [Type] } 
	  | TypeVar Id         -- simple id

type ClassId = Id

data Class = Universe 
	   | ClassName ClassId
	   | Intersection (Set ClassId)

data TypeVarDecl = TypeVarDecl { typeVarId :: Id, typeClass :: Class }

data TypeScheme = TypeScheme [TypeVarDecl] [Type] 

data SymbType = OpType TypeScheme
	      | TypeKind Kind
	      | Class

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symbol] 

data Symbol = Symbol {symbId :: Id, sumbType :: SymbType}

data Variance = CoVar | ContraVar | InVar 

data ExtClass = ExtClass Class Variance

data Kind = Kind { kindArgs :: [ExtClass], kindRes :: Class } 

sort = Kind [] Universe

data GenKind = Free | Generated | Loose deriving (Show,Eq)      

data VarDecl = VarDecl { varId :: Id, varType :: Type }

data TypeBody = Alias Type -- non-recursive
	      | Datatype [Alternative] GenKind GenItems
	      | SubtypeDefn VarDecl Type Term -- a formula

-- type variables correspond to the kind
data TypeDefn = TypeDefn [TypeVarDecl] TypeBody

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

data TypeRel = TypeRel [TypeVarDecl] Type Type

data TypeItem = TypeItem{ typeConstrId :: Id
			, kind :: Kind
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
		     , opType :: TypeScheme
		     , opAttrs :: [OpAttr]
		     , opDefn :: Maybe OpDefn
		     }		      

data TypeOp = OfType | AsType | InType deriving (Eq)     

data Binder = LambdaTotal | LambdaPartial
	    | Forall 
            | Exists | ExistsUnique 
	    deriving (Eq)

data Term = BaseName Id TypeScheme [Type]  -- instance
	  | VarId Id Type Class
          | Application Term [Term] 
	  | Binding Binder [VarDecl] Term
	  | Typed Term TypeOp Type

data SigItem = AClassItem ClassItem
	     | ATypeItem TypeItem
	     | AnOpItem OpItem
