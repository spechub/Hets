module LocalEnv where

type LocalEnv = ([SortItem], [OpItem], 
                [VarDecl],     
                [Axiom],   
                [GenItems],   
                [Freetype])    

-- "local-var-axioms" are a special Term "forall V1,...,V2. F1 /\ F2 /\ ...

type Freetype = SortId   -- synonyms

type Axiom = Term        -- synonyms


-- the (non-empty) list of items which are part of a "sort-gen"
data GenItems = GenItems [ItemId] 
		   deriving (Show,Eq)      

data SortItem = SortItem(SortDecl, SortRels, Maybe SortDefn)
	        deriving (Show,Eq)      

sortId(SortItem(SortDecl(i, _), _, _)) = i

-- the sub- and supertypes of a sort
data SortRels = SortRels([Type], [Type])
		   deriving (Show,Eq)      

data OpItem = OpItem(OpDecl, [OpAttr], Maybe OpDefn) 
	        deriving (Show,Eq)      

opId(OpItem(d, _, _)) = varId(d)
opType(OpItem(d, _, _)) = varType(d)

data OpAttr = AssocOpAttr | CommonOpAttr | IdemOpAttr | UnitOpAttr Term
	       deriving (Show,Eq)

-- operation defined by a Lambda-Term or generated from a datatype
data OpDefn = Definition Term
             | Constructor(SortId, ConsId)
             | Selector (SortId, ConsId, SelId)  
	       deriving (Show,Eq)

-- synonyms to indicate the order of arguments
type ConsId = QualId  
type SelId = QualId   

-- sort defined as predicate subtype or as more or less loose datatype
data SortDefn = SubsortDefn Term -- again binding TERM "forall x : t . p(x)"
               | Datatype ([Alternative], GenKind)
		 deriving (Show,Eq)

-- looseness of a datatype
-- a datatype may (only) be (sub-)part of a "sort-gen"
data GenKind = Free | Generated(GenItems) | Loose
		   deriving (Show,Eq)      

-- full function type (in OpDecl) of constructor 
-- plus redundant (apart from partiality) component types
data Alternative = Construct(OpDecl, [Component]) 
		 | Subsort(Type, DeclNotation) -- subsorts plus notation hint
		   deriving (Show,Eq)      

-- real function type of selector as DeclId
-- invisible Ids will be generated if not given by the user  
data Component = Component(OpDecl)
		   deriving (Show,Eq)      

-- we want to have (at least some builtin) type constructors 
data Type = Type(SortId, [Type])
	    deriving (Show,Eq)

-- function types, product type and the internal bool for predicates
totalFun(t1,t2) = Type(totalFunArrow, [t1,t2])
totalFun  :: (Type, Type) -> Type 
partialFun(t1,t2) = Type(partialFunArrow, [t1,t2])

predicate t = totalFun(t, internalBool)

isPredicate t = isFunType t && resType(t) == internalBool

product l = Type(productSign, l)
isProduct(Type(s, _)) = (s == productSign)

isFunType(Type(s, [_, _])) = (s == totalFunArrow) || (s == partialFunArrow)
isFunType(_) = False

argType(Type(_, [t, _])) = t
resType(Type(_, [_, t])) = t

-- test if a type is first-order
isSort(Type(_, l)) = case l of {[] -> True ; _ -> False}

isFOArgType(t) = isSort(t) || isProduct(t) && 
                  case t of { Type(_,l) -> all isSort l }  

isFOType(t) = isSort(t) || isFunType(t) && isSort(resType(t)) && 
                           isFOArgType(argType(t))

-- one type for terms and formulae
-- op or var possibly applied to no arguments (base-case)
data Term = Application(QualId, [Term], BracketNotation) 
	  | TypedTerm(CastKind, Term, Type)
	  | Binding(Binder, [VarDecl], Term)           
	    deriving (Show,Eq)

type BracketNotation = String -- elaborate more (notation hint)

data CastKind = SortedTerm | Membership | Cast
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
data QualId = QualId(Id, Type, IdKind, QualKind)
		   deriving (Show,Eq)

-- not really necessary (can be looked up)
data IdKind = OpId | PredId | GlobalVar | LocalVar
		   deriving (Show,Eq)      
 
-- may be only the result typ of an op needs to be inferred?
data QualKind = UserGiven | Inferred 
		   deriving (Show,Eq)      

-- declaration of a variable or operation 
data DeclId = DeclId(Id, Type, IdKind, DeclNotation)      
		   deriving (Show,Eq)

varId(DeclId(i, _, _, _)) = i
varType(DeclId(_, t, _, _)) = t

-- synonyms
type VarDecl = DeclId 
type OpDecl = DeclId

-- (single) sort declaration
data SortDecl = SortDecl(SortId, DeclNotation)
		   deriving (Show,Eq)      

-- try to reconstruct notation of (nested) declaration  
data DeclNotation = DeclNotation(Pos, PreviousKeyword)
		   deriving (Show,Eq)

type Pos = (Int, Int) -- line, column

nullPos = (0,0) -- dummy position

type PreviousKeyword = String

-- "sort s"     -> PreviousKeyword(s) = "sort") 
-- "sorts s; t" -> PreviousKeyword(t) = ";")
-- "sorts s, t" -> PreviousKeyword(t) = "'")
-- for iso-decl or subsort-decl PreviousKeyword could be "<" or "="

-- Ids uniquely identify sorts
type SortId = Id

-- mixfix ingredients
data TokenOrPlace = Place Pos | Token Pos String -- start position
		      deriving (Show,Eq)
-- Ids in a compound list refer to sorts or operations  
data ItemId = Sort SortId | Operation QualId
		   deriving (Show,Eq)      

-- an identifier may be mixfix (though not for a sort) and compound 
data Id = Id([TokenOrPlace],[ItemId])
		   deriving (Show,Eq)      

-- simple Id
simpleId(s) = Id([Token nullPos s],[]) 

totalFunArrow = simpleId("->")
partialFunArrow = simpleId("->?")
productSign = simpleId("*")

sortAsType(s) = Type(s, []) 
internalBool = sortAsType(simpleId("%logical")) -- % to make it invisible


