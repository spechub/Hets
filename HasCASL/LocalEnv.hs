module LocalEnv where

import Id
import Maybe
import Type
import Term

-- the sub- and supertypes of a sort
data SortRels = SortRels [Type] [Type] deriving (Show)      

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symb] 

-- real function type of a selector as Decl
data Component = Component Decl deriving (Show)      

-- full function type (in Decl) of constructor 
-- plus redundant (apart from partiality) component types
data Alternative = Construct Decl [Component] 
		 | Subsort Decl   
		   deriving (Show)      

-- looseness of a datatype
-- a datatype may (only) be (sub-)part of a "sort-gen"
data GenKind = Free | Generated | Loose deriving (Show,Eq)      

-- sort defined as predicate subtype or as more or less loose datatype
data SortDefn = SubsortDefn Term   -- binding Term "{ x : t | p(x) }"
              | Datatype [Alternative] GenKind GenItems

defStr = "::="
barChar = '|'

instance Show SortDefn where
    showsPrec _ (SubsortDefn t) = showSignStr equalStr . shows t  
    showsPrec _ (Datatype alts _ _) = 
	showSignStr defStr . showSepList (showChar barChar) shows alts  

data SortItem = SortItem { sortDecl :: Decl
			 , sortRels :: SortRels
                         , sortDef  :: Maybe SortDefn
			 , sortAn   :: [Anno]
			 }
sortStr = "sort"
showSortItem (SortItem decl (SortRels le ge) def an) = 
    showSignStr sortStr . shows decl 
	  . shows le . shows ge
	  . showPlainList (maybeToList def)
	  . showAnno an

instance Show SortItem where
    showsPrec _ = showSortItem
    showList = showSepList (showString "\n") shows


assocStr = "assoc"
commStr = "comm"
idemStr = "idem"
unitStr = "unit"

data OpAttr = AssocOpAttr | CommOpAttr | IdemOpAttr | UnitOpAttr Term

instance Show OpAttr where
     showsPrec _ AssocOpAttr = showString assocStr
     showsPrec _ CommOpAttr = showString commStr
     showsPrec _ IdemOpAttr = showString idemStr
     showsPrec _ (UnitOpAttr t) = showSignStr unitStr . shows t
     showList = showString . concat . map (\a -> ',' : show a)

-- synonyms to indicate the order of arguments
type SortId = Id
type ConsSymb = Symb  
type SelSymb = Symb  

-- operation defined by a Lambda-Term or generated from a datatype
-- a selector may cover several constructors/alternatives 
data OpDefn = Definition Term
            | Constructor SortId ConsSymb
            | Selector SortId [ConsSymb] SelSymb
	      deriving (Show)

data OpItem = OpItem { opDecl :: Decl
		     , opAttrs :: [OpAttr]
		     , opDefn :: (Maybe OpDefn)
		     , opAn :: [Anno]
		     }

showOpItem (OpItem decl attrs def an) =
    showSignStr opStr . shows decl . shows attrs 
	  . showPlainList (maybeToList def)
	  . showAnno an

instance Show OpItem where
    showsPrec _ = showOpItem

type Axiom = Term        -- synonyms
-- "local-var-axioms" are a special Term "forall V1,...,V2. F1 /\ F2 /\ ...

data AnItem = ASortItem SortItem
	    | AnOpItem OpItem
	    | AVarDecl VarDecl
	    | AnAxiom Axiom
	    | BeginGen | EndGen

showItem(ASortItem s) = shows s
showItem(AnOpItem o) = shows o
showItem(AVarDecl d) = shows d
showItem(AnAxiom t) = shows t
showItem BeginGen = showString "generated{"
showItem EndGen = showString "}%[generated]%"

instance Show AnItem where
	showsPrec _ = showItem
	showList = showSepList (showChar '\n') shows 

updateAn :: AnItem -> [Anno] -> AnItem
updateAn(ASortItem s) an = ASortItem (s {sortAn = an})
updateAn(AnOpItem o) an = AnOpItem (o {opAn = an})
updateAn(AVarDecl d) an = AVarDecl (d {declAn = an})
updateAn(AnAxiom (Annotated t _)) an = AnAxiom (Annotated t an)
updateAn(AnAxiom t) an = AnAxiom (Annotated t an)

type Ast = [AnItem]

addAn :: Ast -> [Anno] -> Ast
addAn [] an = []
addAn (EndGen:r) an = EndGen : addAn r an
addAn (BeginGen:r) an = BeginGen : addAn r an
addAn (h:r) an = updateAn h an : r

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

addToLastGenItem :: Env -> Symb -> Env
addToLastGenItem (Env s o v a (h:r)) i = 
    Env s o v a ((i:h):r)

toEnv _ env [] = env
toEnv _ env (BeginGen:r)  = toEnv True (env {generates = [] : generates env}) r
toEnv _ env (EndGen:r)  = toEnv False env r
toEnv b env ((ASortItem s):r) = 
    let i = symb (sortDecl s)
	env' = if b then addToLastGenItem env i else env
    in toEnv b (env' {sorts = s : sorts env'}) r
toEnv b env ((AnOpItem o):r) = 
    let i = symb (opDecl o)
	env' = if b then addToLastGenItem env i else env
    in toEnv b (env' {ops = o : ops env'}) r
toEnv b env ((AVarDecl v):r) = toEnv b (env {vars = v : vars env}) r
toEnv b env ((AnAxiom a):r) = toEnv b (env {axioms = a : axioms env}) r

empty = Env [] [] [] [] []
