module Ast where

import Id
import Lexer
import Maybe
import Parsec
import ParseType
import ParseTerm
import Type
import Term
import Token

type SortId = Id
type OpId = Id
type VarId = Id

barChar = '|'
sortStr = "sort"

type Axiom = Term

data BasicItems = SigItems SigItems
		| FreeDatatypeItems [DatatypeDecl]
                | SortGen [SigItems]
		| VarItems [VarDecl]
		| LocalVarDecl [VarDecl] [Axiom] 
		| Axioms [Axiom]

data SigItems = SortItems Keyword [SortItem]
	      | OpItems Keyword [OpItem]
	      |	DatatypeItems [DatatypeDecl]
              deriving (Show)

data SortItem = SubsortDecl [SortId] (Maybe Type)
	      | IsoDecl [SortId]
	      |	SubsortDefn SortId VarId Type Term
	      | AnnotatedSortItem SortItem [Anno]

showSortItem (SubsortDecl l Nothing) = showCommaList l 
showSortItem (SubsortDecl l (Just t)) = 
    showCommaList l . showSignStr lessStr . showSign t  

showSortItem (IsoDecl l) = 
    showSepList (showSignStr equalStr) showSign l 

showSortItem (AnnotatedSortItem s _) = shows s
showSortItem (SubsortDefn s _ _ e) = 
    shows s. showSignStr equalStr . shows e

instance Show SortItem where
    showsPrec _ = showSortItem

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

data OpItem = OpItem [OpId] Type [OpAttr] (Maybe Term) [Anno]
	    deriving (Show)

data Component = Component Decl deriving (Show)      

-- full function type (in Decl) of constructor 
data Alternative = Construct Decl [Component] 
		 | Subsorts [SortId]
		   deriving (Show) 

data DatatypeDecl = DatatypeDecl SortId [Alternative] deriving (Show)    

class Annotatable a where
    annotate :: a -> [Anno] -> a

instance Annotatable OpItem where
    annotate (OpItem os t as def _) l = OpItem os t as def l 

instance Annotatable SortItem where
    annotate (AnnotatedSortItem s _) l = AnnotatedSortItem s l
    annotate s l = AnnotatedSortItem s l

commaSortDecl :: SortId -> Parser SortItem
commaSortDecl s = do { l <- comma >> (sortId `sepBy1` comma)
		     ; let l' = s : l in
		       subSortDecl l'
		       <|> return (SubsortDecl l' Nothing)
		     }

isoDecl :: SortId -> Parser SortItem
isoDecl s = do { e <- equal
               ; subSortDefn s
		 <|>
		 (do { l <- sortId `sepBy1` equal
		     ; return (IsoDecl (s:l))
		     })
	       }

subSortDefn :: SortId -> Parser SortItem
subSortDefn s = do { o <- oBrace
		   ; v <- varId
		   ; t <- colon >>= funType
		   ; dot <|> bar	 
		   ; e <- parseTerm
		   ; cBrace
		   ; let f = Binding SupersortVar [Decl (Symb [v] t) o []] e
		     in return (SubsortDefn s v t f)
		   }

subSortDecl :: [SortId] -> Parser SortItem
subSortDecl l = do { s <- lessSign >>= funType
		   ; return (SubsortDecl l (Just s))
		   }

sortItem :: Parser SortItem
sortItem = do { s <- sortId
	      ; subSortDecl [s]
		<|>
		commaSortDecl s
		<|>
                isoDecl s
		<|> 
		return (SubsortDecl [s] Nothing)
	      } 		

sortItems = do { key <- pluralKeyword sortStr
	       ; l <- itemAux sortItem
	       ; return (SortItems key l)
	       }

pluralKeyword s = makeToken (string s <++> option "" (string "s"))

optSemi = bind (\ x y -> (x, y)) (option Nothing (fmap Just semi)) ann

dot = toKey [dotChar] <|> toKey middleDotStr <?> "dot"
bar = toKey [barChar]
equal = toKey equalStr

isStartKeyword s = s `elem` [dotChar]:middleDotStr:casl_reserved_words

lookAheadItemKeyword :: a -> Parser a
lookAheadItemKeyword a = 
    do { c <- lookAhead (many (oneOf (['0'..'9'] ++ "'" ++ caslLetters))
			 <|> many (oneOf signChars))
       ; if isStartKeyword c then return a else unexpected c
       }

itemAux :: Annotatable a => (Parser a) -> Parser [a]
itemAux itemParser = 
    do { i <- itemParser
       ; (m, an) <- optSemi
       ; let i' = if null an then i else annotate i an
	 in case m of Nothing -> return [i']
                      Just _ -> try (lookAheadItemKeyword [i'])
	                        <|> 
	                        do { l <- itemAux itemParser
				   ; return (i':l)
				   }
       }




