module Term where

import Char (isLower)
import Id
import Type

-- symbols uniquely identify signature items 
data Symb = Symb { symbId :: Id
		 , symbType :: Type 
		 } deriving (Eq, Ord)

showSymb :: Symb -> ShowS
showSymb (Symb i Sort) = shows i
showSymb (Symb i t) = shows i . showChar ':' . shows t

instance Show Symb where
    showsPrec _ = showSymb

-- try to reconstruct notation of (nested) declaration  
type DeclNotation = Keyword 
-- "sort s"     -> previous keyword(s) = "sort") 
-- "sorts s; t" -> previous keyword(t) = ";")
-- "sorts s, t" -> previous keyword(t) = ",")
-- for iso-decl or subsort-decl PreviousKeyword could be "<" or "="

type Anno = String

-- declaration of a variable or operation 
data Decl = Decl { symb :: Symb
		 , nota :: DeclNotation
		 , declAn :: [Anno]
		 } deriving (Eq)

showDecl (Decl s n a) = 
    shows n . showChar ' ' 
    . showSymb s
    . (if null a then showString "" 
       else showChar ';' . showString (unwords a) . showChar '\n')  

instance Show Decl where
    showsPrec _ = showDecl

-- for faster lookup
type DeclLevel = Int
-- 0 -> sign, 1 -> var, ... local vars 

-- may be only the result typ of an op needs to be inferred?
data QualKind = UserGiven | Inferred 
		   deriving (Show,Eq)      

-- application of a variable or operation
data QualId = QualId Symb DeclLevel QualKind deriving (Show,Eq)

-- synonym
type VarDecl = Decl 

data Totality = Partial | Total deriving (Show,Eq)

-- maybe also Ids or keywords
data Binder = Lambda Totality | ArgDecl | SupersortVar
	    | Forall 
            | Exists | ExistsUnique
	    deriving (Show,Eq)      

data TypeOp = OfType | AsType | InType deriving (Show,Eq)     

-- one type for terms and formulae
-- op or var possibly applied to no arguments (base-case)
data Term = BaseName QualId
          | Application Term [Term] [Keyword] -- notation hint
	  | Binding Binder [VarDecl] Term [Anno]           
	  | Typed Term TypeOp Type
	    deriving (Show,Eq)
