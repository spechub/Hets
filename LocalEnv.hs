module LocalEnv where

import Id

-- we want to have (at least some builtin) type constructors 
-- for uniformity sorts get type "Sort"
-- "Sort -> Sort" would be the type/kind of a type constructor
data Type = Type(Id, [Type])
          | Sort
	    deriving (Show, Eq, Ord)

-- function types, product type and the internal bool for predicates
totalFun(t1,t2) = Type(totalFunArrow, [t1,t2])
totalFun  :: (Type, Type) -> Type 
partialFun(t1,t2) = Type(partialFunArrow, [t1,t2])

predicate t = totalFun(t, internalBool)

isPredicate t = isFunType t && resType(t) == internalBool

product l = Type(productSign, l)
isProduct(Type(s, _)) = (s == productSign)
isPoduct(_) = False

isFunType(Type(s, [_, _])) = (s == totalFunArrow) || (s == partialFunArrow)
isFunType(_) = False

argType(Type(_, [t, _])) = t
resType(Type(_, [_, t])) = t

-- test if a type is first-order
isSort(Type(_, l)) = case l of {[] -> True ; _ -> False}
isSort(Sort) = True -- but not a the type of a function 

isFOArgType(t) = isSort(t) || isProduct(t) && 
                  case t of { Type(_,l) -> all isSort l }  

isFOType(t) = isSort(t) || isFunType(t) && isSort(resType(t)) && 
                           isFOArgType(argType(t))

-- symbols uniquely identify signature items 
data Symb = Symb(Id, Type) deriving (Show, Eq, Ord)

-- try to reconstruct notation of (nested) declaration  
data DeclNotation = PreviousKeyword Keyword deriving (Show,Eq)
-- "sort s"     -> PreviousKeyword(s) = "sort") 
-- "sorts s; t" -> PreviousKeyword(t) = ";")
-- "sorts s, t" -> PreviousKeyword(t) = "'")
-- for iso-decl or subsort-decl PreviousKeyword could be "<" or "="

-- declaration of a variable or operation 
data Decl = Decl(Symb, DeclNotation)      
		   deriving (Show,Eq)

-- the sub- and supertypes of a sort
data SortRels = SortRels([Type], [Type]) deriving (Show,Eq)      


type LocalEnv = ([SortItem], [OpItem], 
                [VarDecl],     
                [Axiom],   
                [GenItems])


-- "local-var-axioms" are a special Term "forall V1,...,V2. F1 /\ F2 /\ ...

type Axiom = Term        -- synonyms

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symb] 

data SortItem = SortItem(Decl, SortRels, Maybe SortDefn)
	        deriving (Show,Eq)      

data OpItem = OpItem(Decl, [OpAttr], Maybe OpDefn) 
	        deriving (Show,Eq)      

data OpAttr = AssocOpAttr | CommonOpAttr | IdemOpAttr | UnitOpAttr Term
	       deriving (Show,Eq)

-- operation defined by a Lambda-Term or generated from a datatype
data OpDefn = Definition Term
            | Constructor(SortId, ConsId)
            | Selector (SortId, ConsId, SelId)  
	      deriving (Show,Eq)

-- synonyms to indicate the order of arguments
type SortId = Symb
type ConsId = Symb  
type SelId = Symb  

-- sort defined as predicate subtype or as more or less loose datatype
data SortDefn = SubsortDefn Term -- again binding TERM "forall x : t . p(x)"
              | Datatype ([Alternative], GenKind, GenItems)
	        deriving (Show,Eq)

-- looseness of a datatype
-- a datatype may (only) be (sub-)part of a "sort-gen"
data GenKind = Free | Generated | Loose deriving (Show,Eq)      

-- full function type (in OpDecl) of constructor 
-- plus redundant (apart from partiality) component types
data Alternative = Construct(Decl, [Component]) 
		 | Subsort Decl   
		   deriving (Show,Eq)      

-- real function type of selector as DeclId
-- invisible Ids will be generated if not given by the user  
data Component = Component Decl deriving (Show,Eq)      


-- one type for terms and formulae
-- op or var possibly applied to no arguments (base-case)
-- typed term is also a special application
data Term = BaseName QualId
          | Application(Term, [Term], [Keyword]) -- notation hint
	  | Binding(Binder, [VarDecl], Term)           
	    deriving (Show,Eq)

-- may be expand variants 
data Binder = Lambda(VarNotation, Totality)
	    | Forall(ForallNotation) 
            | Exists(ExistsKind)
		   deriving (Show,Eq)      

-- "opName(x1:t1, x2:t2, ...)=" or "opname = \x1:t1, x2:t2, ... ."
data VarNotation = ArgDecl | LambdaVars
		   deriving (Show,Eq)      

-- differentiate between usual forall, local-var-axioms, subsort-defn 
data ForallNotation = Plain | LocalVars | SupersortVar 
		   deriving (Show,Eq)      

data ExistsKind = Any | Unique
		   deriving (Show,Eq)      

data Totality = Partial | Total

		   deriving (Show,Eq)      

-- application of a variable or operation
data QualId = QualId(Symb, DeclLevel, QualKind) deriving (Show,Eq)

-- for faster lookup
type DeclLevel = Int
-- 0 -> sign, 1 -> var, ... local vars 
 
-- may be only the result typ of an op needs to be inferred?
data QualKind = UserGiven | Inferred 
		   deriving (Show,Eq)      


-- synonyms
type VarDecl = Decl 

-- mixfix ingredients


-- simple Id
simpleId(s) = Id([Token(s, nullPos)],[]) 

totalFunArrow = simpleId("->")
partialFunArrow = simpleId("->?")
productSign = simpleId("*")

sortAsType(s) = Type(s, []) 
internalBool = sortAsType(simpleId("%logical")) -- % to make it invisible


