module Term where

import Char (isLower)
import Id
import Type

type Anno = String

showAnno an = showSepList (showString "") showString an

-- declaration of variables
data Decl = Decl { declIds :: [Id]
		 , declType :: Type
		 , declPos :: [Pos] -- comma positions + colon position
		 }

instance Show Decl where
    showsPrec _ (Decl is t _ ) = 
	showCommaList is . showSignStr ([colonChar]) . shows t 
    showList = showSepList (showChar ';') shows

colonChar = ':'

showCommaList :: Show a => [a] -> ShowS
showCommaList = showSepList (showChar ',') showSign

varStr = "var"
predStr = "pred"
opStr = "op"

data QualKind = VarQ | PredQ | OpQ
		   deriving (Eq)      
 
instance Show QualKind where
    showsPrec _ VarQ = showString varStr
    showsPrec _ PredQ = showString predStr
    showsPrec _ OpQ = showString opStr

-- application of a variable or operation
data QualId = QualId { qualKind :: QualKind
		     , qualId :: Id
		     , qualType :: Type 
		     , qualPos :: [Pos] 
		       -- open Paren, keyword, colon, close Paren 
		     } deriving (Eq)

instance Show QualId where
    showsPrec _ = showQualId

showQualId(QualId k i t _) =
    showParen True (showSign k . showSign i . 
		    showSignStr (if isPartialId t then colonChar:partialSuffix
				 else [colonChar]) . showSign t)

isPartialId (PartialType _) = True 
isPartialId _ = False

-- synonym
type VarDecl = Decl 

exStr = "exists"
allStr = "forall"
lamStr = "\\" 

-- maybe also Ids or keywords
data Binder = LambdaTotal | LambdaPartial
	    | Forall 
            | Exists | ExistsUnique
	    deriving (Eq)

instance Show Binder where
    showsPrec _ LambdaPartial = showString lamStr     
    showsPrec _ LambdaTotal = showString lamStr
    showsPrec _ Forall = showString allStr
    showsPrec _ Exists = showString exStr
    showsPrec _ ExistsUnique = showString (exStr ++ totalSuffix)
 
isTotalLambda LambdaTotal = True
isTotalLambda _ = False

data TypeOp = OfType | AsType | InType deriving (Eq)     

instance Show TypeOp where
    showsPrec _ OfType = showChar colonChar
    showsPrec _ AsType = showString "as"
    showsPrec _ InType = showString "in"

data BracketKind = Parens | Squares | Braces

showBracket::BracketKind -> ShowS -> ShowS
showBracket Parens s = showParen True s 
showBracket Squares s = showChar '[' . s . showChar ']' 
showBracket Braces s = showChar '{' . s . showChar '}' 

-- one type for terms and formulae
-- op or var possibly applied to no arguments (base-case)
-- only the top-level term may be annotated with (non-empty) annotations
-- MixTerm is only used between parsing and static analysis 
-- as first term of an Application 

data Term = Qualified QualId
	  | SimpleTerm Token -- Place, No-BracketToken, Literal
          | Application BracketKind [Term] [Pos] -- open, commas, close
          | MixTerm [Term]
	  | Binding Binder [VarDecl] Term [Pos] -- quant, semicolons, dot
	  | TypeInfo TypeOp Type [Pos] -- colon

instance Show Term where
    showsPrec _ = showTerm
    showList = showCommaList

showTerm (Qualified q) = shows q
showTerm (SimpleTerm t) = shows t

showTerm (Application b ts _) = 
    showBracket b (showCommaList ts)

showTerm (MixTerm ts) = showSepList (showString "") showSign ts

showTerm (Binding b decls term _) = 
    showSign b . showSign decls 
		   . showSignStr (if isTotalLambda b then dotChar:totalSuffix 
		     else middleDotStr) . shows term

showTerm (TypeInfo op t _) = showSign op . shows t 

middleDotStr = "\183"
dotChar = '.'

