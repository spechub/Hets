module LocalEnv where

import Id
import Type
import Term

-- the sub- and supertypes of a sort
data SortRels = SortRels([Type], [Type]) deriving (Show,Eq)      

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symb] 

-- real function type of a selector as Decl
data Component = Component Decl deriving (Show,Eq)      

-- full function type (in Decl) of constructor 
-- plus redundant (apart from partiality) component types
data Alternative = Construct(Decl, [Component]) 
		 | Subsort Decl   
		   deriving (Show,Eq)      

-- looseness of a datatype
-- a datatype may (only) be (sub-)part of a "sort-gen"
data GenKind = Free | Generated | Loose deriving (Show,Eq)      

-- sort defined as predicate subtype or as more or less loose datatype
data SortDefn = SubsortDefn Term   -- binding Term "{ x : t | p(x) }"
              | Datatype ([Alternative], GenKind, GenItems)
	        deriving (Show,Eq)

data SortItem = SortItem(Decl, SortRels, Maybe SortDefn)
	        deriving (Show,Eq)

data OpAttr = AssocOpAttr | CommonOpAttr | IdemOpAttr | UnitOpAttr Term
	       deriving (Show,Eq)

-- synonyms to indicate the order of arguments
type SortId = Symb
type ConsId = Symb  
type SelId = Symb  

-- operation defined by a Lambda-Term or generated from a datatype
-- a selector may cover several constructors/alternatives 
data OpDefn = Definition Term
            | Constructor(SortId, ConsId)
            | Selector (SortId, [ConsId], SelId)  
	      deriving (Show,Eq)

data OpItem = OpItem(Decl, [OpAttr], Maybe OpDefn) 
	        deriving (Show,Eq)      

type Axiom = Term        -- synonyms
-- "local-var-axioms" are a special Term "forall V1,...,V2. F1 /\ F2 /\ ...

type LocalEnv = ([SortItem], [OpItem], 
                [VarDecl],     
                [Axiom],   
                [GenItems])

