module Term where

import Id
import Type

-- symbols uniquely identify signature items 
data Symb = Symb(Id, Type) deriving (Show, Eq, Ord)

-- try to reconstruct notation of (nested) declaration  
data DeclNotation = PreviousKeyword Keyword deriving (Show,Eq)
-- "sort s"     -> PreviousKeyword(s) = "sort") 
-- "sorts s; t" -> PreviousKeyword(t) = ";")
-- "sorts s, t" -> PreviousKeyword(t) = "s")
-- for iso-decl or subsort-decl PreviousKeyword could be "<" or "="

-- declaration of a variable or operation 
data Decl = Decl(Symb, DeclNotation) deriving (Show,Eq)

-- for faster lookup
type DeclLevel = Int
-- 0 -> sign, 1 -> var, ... local vars 

-- may be only the result typ of an op needs to be inferred?
data QualKind = UserGiven | Inferred 
		   deriving (Show,Eq)      

-- application of a variable or operation
data QualId = QualId(Symb, DeclLevel, QualKind) deriving (Show,Eq)

-- synonym
type VarDecl = Decl 

data Totality = Partial | Total deriving (Show,Eq)

-- maybe also Ids or keywords
data Binder = Lambda(Totality) | ArgDecl | SupersortVar
	    | Forall 
            | Exists | ExistsUnique
	    deriving (Show,Eq)      

-- one type for terms and formulae
-- op or var possibly applied to no arguments (base-case)
-- a typed term is also a special application
data Term = BaseName QualId
          | Application(Term, [Term], [Keyword]) -- notation hint
	  | Binding(Binder, [VarDecl], Term)           
	    deriving (Show,Eq)
