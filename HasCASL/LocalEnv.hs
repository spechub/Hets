module LocalEnv where

import Id
import Type
import Term

-- the sub- and supertypes of a sort
data SortRels = SortRels [Type] [Type] deriving (Show,Eq)      

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symb] 

-- real function type of a selector as Decl
data Component = Component Decl deriving (Show,Eq)      

-- full function type (in Decl) of constructor 
-- plus redundant (apart from partiality) component types
data Alternative = Construct Decl [Component] 
		 | Subsort Decl   
		   deriving (Show,Eq)      

-- looseness of a datatype
-- a datatype may (only) be (sub-)part of a "sort-gen"
data GenKind = Free | Generated | Loose deriving (Show,Eq)      

-- sort defined as predicate subtype or as more or less loose datatype
data SortDefn = SubsortDefn Term   -- binding Term "{ x : t | p(x) }"
              | Datatype [Alternative] GenKind GenItems
	        deriving (Show,Eq)

data SortItem = SortItem { sortDecl :: Decl
			 , sortRels :: SortRels
                         , sortDef  :: Maybe SortDefn
			 , sortAn   :: [Anno]
			 } deriving (Eq)


showSortItem (SortItem decl rels def an) = 
    shows decl . showChar ' ' . showParen True (shows rels)
	  . showChar ' ' . (case def of Nothing -> showString ""
				        Just x -> showParen True (shows x))
	  . showString (unwords an) . showChar '\n'

instance Show SortItem where
    showsPrec _ = showSortItem
    showList [] = showString ""
    showList (x:r) = shows x . showList r

data OpAttr = AssocOpAttr | CommonOpAttr | IdemOpAttr | UnitOpAttr Term
	       deriving (Show,Eq)

-- synonyms to indicate the order of arguments
type SortId = Id
type ConsSymb = Symb  
type SelSymb = Symb  

-- operation defined by a Lambda-Term or generated from a datatype
-- a selector may cover several constructors/alternatives 
data OpDefn = Definition Term
            | Constructor SortId ConsSymb
            | Selector SortId [ConsSymb] SelSymb
	      deriving (Show,Eq)

data OpItem = OpItem Decl [OpAttr] (Maybe OpDefn) [Anno]
	        deriving (Show,Eq)      

type Axiom = Term        -- synonyms
-- "local-var-axioms" are a special Term "forall V1,...,V2. F1 /\ F2 /\ ...

data Env = Env { sorts :: [SortItem] 
	       , ops :: [OpItem]
	       , vars :: [VarDecl]     
	       , axioms :: [Axiom]   
	       , generates :: [GenItems]
	       } deriving ()

showEnv (Env s o v a g) =
    shows (reverse s). shows o. shows v. shows a . shows g

instance Show Env where
    showsPrec _ = showEnv

empty = Env [] [] [] [] []
