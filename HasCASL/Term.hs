module Term where

import Char (isLower)
import Id
import Type

-- symbols uniquely identify signature items 
data Symb = Symb { symbId :: Id
		 , symbType :: Type 
		 } 
	    deriving (Eq, Ord)

showSymb :: Symb -> ShowS
showSymb (Symb i Unknown) = shows i
showSymb (Symb i Sort) = shows i
showSymb (Symb i (PartialType v)) = 
    showSign i . showSignStr (colonChar:partialSuffix) . shows v
showSymb (Symb i t) = showSign i . showSignStr [colonChar] . shows t

instance Show Symb where
    showsPrec _ = showSymb

-- try to reconstruct notation of (nested) declaration  
type DeclNotation = Keyword 
-- "sort s"     -> previous keyword(s) = "sort") 
-- "sorts s; t" -> previous keyword(t) = ";")
-- "sorts s, t" -> previous keyword(t) = ",")
-- for iso-decl or subsort-decl PreviousKeyword could be "<" or "="

type Anno = String

showAnnotation :: [Anno] -> ShowS
showAnnotation [] = showString "" 
showAnnotation an = showChar ';' . showString (unwords an) . showChar '\n'

-- declaration of a variable or operation 
data Decl = Decl { symb :: Symb
		 , nota :: DeclNotation
		 , declAn :: [Anno]
		 } deriving (Eq)

showDecl (Decl s n an) = 
    shows n . showChar ' ' 
    . showSymb s
    . showAnnotation an

showShortDecl (Decl s _ _) = showSymb s

instance Show Decl where
    showsPrec _ = showShortDecl
    showList = showSepList (showChar ';') shows

-- for faster lookup
type DeclLevel = Int
-- 0 -> sign, 1 -> var, ... local vars 

-- may be only the result typ of an op needs to be inferred?
data QualKind = UserGiven | Inferred 
		   deriving (Show,Eq)      
 
varStr = "var"
opStr = "op"
predStr = "pred"

-- application of a variable or operation
data QualId = QualId Symb DeclLevel QualKind deriving (Eq)

showShortQualId(QualId s n UserGiven) =
    showParen True ((if n == 1 then showSignStr varStr
		      else if isPredicate (symbType s) then showSignStr predStr
		      else showSignStr opStr)
		    . showSymb s) 

showShortQualId(QualId s _ _) = showSymb s

instance Show QualId where
    showsPrec _ = showShortQualId

-- synonym
type VarDecl = Decl 

data Totality = Partial | Total deriving (Show,Eq)

exStr = "exists"
allStr = "forall"
lamStr = "lambda" 

-- maybe also Ids or keywords
data Binder = Lambda Totality | ArgDecl | SupersortVar
	    | Forall 
            | Exists | ExistsUnique
	    deriving (Eq)

showBinder (Lambda Partial) = showSignStr lamStr     
showBinder (Lambda Total) = showSignStr (lamStr ++ totalSuffix)
showBinder ArgDecl = showSignStr "(...):" 
showBinder SupersortVar = showSignStr "{....}"
showBinder Forall = showSignStr allStr
showBinder Exists = showSignStr exStr
showBinder ExistsUnique = showSignStr (exStr ++ totalSuffix)
 
instance Show Binder where
    showsPrec _ = showBinder

asStr = "as"
inStr = "in"

data TypeOp = OfType | AsType | InType deriving (Eq)     

showTypeOp OfType = showSignStr [colonChar]
showTypeOp AsType = showSignStr asStr 
showTypeOp InType = showSignStr inStr 

instance Show TypeOp where
    showsPrec _ = showTypeOp

-- one type for terms and formulae
-- op or var possibly applied to no arguments (base-case)
-- only the top-level term may be annotated with (non-empty) annotations
-- MixTerm is only used between parsing and static analysis 
-- as first term of an Application 
data Term = BaseName QualId
          | Application Term [Term] [Keyword] -- notation hint
	  | Binding Binder [VarDecl] Term
	  | Typed Term TypeOp Type
          | Annotated Term [Anno]
	  | MixTerm
	    deriving (Eq)

showTerm (BaseName q) = showShortQualId q

showTerm (Application MixTerm ts [op, cl]) = 
    shows op . showSepList (showChar ',') showTerm ts . shows cl
showTerm (Application MixTerm ts []) = 
    showSepList (showString "") showSign ts
showTerm (Application t ts _) = showTerm t . showParen True (shows ts)

showTerm (Binding ArgDecl decls (Typed term co t)) = 
    showParen (not (null decls)) (shows decls)
		  . showSignStr 
			(if isPartialFunType t then colonChar:partialSuffix 
			 else [colonChar])
		  . showSign t . showSignStr "=" . showSign term  

showTerm (Binding SupersortVar decls term) = 
    showSignStr "{" . showSign decls . showSignStr "\183"
		   . showSign term . showString "}"
    
showTerm (Binding (Lambda Total) decls term) = 
    showSignStr lamStr . showSign decls 
		   . showSignStr ("\183!") . showTerm term

showTerm (Binding b decls term) = 
    showBinder b . showSign decls 
		   . showSignStr "\183" . showTerm term

showTerm (Typed MixTerm op t) = showTypeOp op . shows t 
showTerm (Typed term op t) = showSign term . showTypeOp op . shows t 

showTerm (Annotated t an) = showTerm t . showAnnotation an
showTerm MixTerm = showString "!MIX!"

instance Show Term where
    showsPrec _ = showTerm
    showList l = showSepList (showChar ',') showTerm l
  
isBaseName (BaseName _) = True
isBaseName _ = False
