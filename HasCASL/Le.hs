
{- HetCATS/HasCASL/Le.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   abstract syntax after/during static analysis
-}

module Le where

import Id
import As

-----------------------------------------------------------------------------
-- Symbols
-----------------------------------------------------------------------------

data SymbType = OpType TypeScheme
	      | TypeKind Kind
	      | Class
		deriving (Show, Eq)      

data Symbol = Symbol {symbId :: Id, sumbType :: SymbType} deriving (Show, Eq)

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symbol] 

-----------------------------------------------------------------------------
-- Items
-----------------------------------------------------------------------------

data GenKind = Free | Generated | Loose deriving (Show, Eq)      

data TypeBody = Alias Type -- non-recursive
	      | Datatype [Le.Alternative] GenKind GenItems
	      | SubtypeDefn VarDecl Type Term -- a formula
		deriving (Show, Eq)

-- type variables correspond to the kind
data TypeDefn = TypeDefn [TypeVarDecl] TypeBody deriving (Show, Eq)

-- full function type of constructor (result sort is the data type)
data Alternative = Construct Id Type [Component] 
		 | Subtype Type
		   deriving (Show, Eq)

-- full function type of a selector (result sort is component sort)
data Component = Component (Maybe Id) Type  deriving (Show, Eq)

data ClassItem = ClassItem { classId :: ClassName
			   , superClasses :: [ClassName]
			   , classDefn :: Class
			   , instances :: [Qual Pred]
                           , classBody :: [SigItem]
			   } deriving (Show, Eq)

newClassItem :: ClassName -> Le.ClassItem
newClassItem cid = Le.ClassItem cid [] (Intersection [] []) [] []

showClassList :: [ClassName] -> ShowS
showClassList is = showParen (length is > 1)
		   $ showSepList ("," ++) ((++) . tokStr) is


data TypeRel = TypeRel [TypeVarDecl] Type Type deriving (Show, Eq)

data TypeItem = TypeItem{ typeConstrId :: Id
			, itemKind :: Kind
			, subtypes :: [TypeRel]
			, supertypes :: [TypeRel]
			, typeDefn :: Maybe TypeDefn
			} deriving (Show, Eq)

type ConsId = Symbol
type SelId = Symbol

data OpDefn = OpDef [VarDecl] Term
            | Constr ConsId
            | Select [ConsId] SelId
	      deriving (Show, Eq)

data OpItem = OpItem { opId :: Id
		     , opType :: TypeScheme
		     , opAttrs :: [OpAttr]
		     , opDefn :: Maybe OpDefn
		     } deriving (Show, Eq)	      

data SigItem = AClassItem Le.ClassItem
	     | ATypeItem Le.TypeItem
	     | AnOpItem Le.OpItem
	       deriving (Show, Eq)
