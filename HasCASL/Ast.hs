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

type TypeId = Id
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

instance Show BasicItems where
    showsPrec _ (SigItems s) = shows s

data SigItems = SortItems [SortItem] [Pos] -- "sort", semis
	      | OpItems [OpItem] [Pos]     -- "op", semis
--	      | PredItems [PredItem]
	      |	DatatypeItems [DatatypeDecl]
--              deriving (Show)

instance Show SigItems where
    showsPrec _ (SortItems l _) = shows l
    showList l = showSignStr sortStr . showSepList (showChar '\n') shows l

data SortItem = SortDecl [TypeId] [Pos]            -- commas
              | SubsortDecl [TypeId] Type [Pos]    -- commas, less
	      | IsoDecl [TypeId] [Pos]             -- equal signs
	      |	SubsortDefn TypeId VarDecl Term [Pos] 
	                                           -- equal, oBrace, dot, cBrace
	      | AnnotatedSortItem SortItem [Anno]

instance Show SortItem where
    showsPrec _ = showSortItem
    showList = showSepList (showChar ';') shows

showSortItem (SortDecl l _) = showCommaList l 
showSortItem (SubsortDecl l t _) = 
    showCommaList l . showSignStr lessStr . showSign t  

showSortItem (IsoDecl l _) = 
    showSepList (showSignStr equalStr) showSign l 

showSortItem (AnnotatedSortItem s _) = shows s
showSortItem (SubsortDefn s d e _) = 
    shows s. showSignStr equalStr . showBracket Braces 
	      (showSign d . showSignStr middleDotStr. shows e)

data OpBinAttr = AssocOpAttr | CommOpAttr | IdemOpAttr 

instance Show OpBinAttr where
     showsPrec _ AssocOpAttr = showString "assoc"
     showsPrec _ CommOpAttr = showString "comm"
     showsPrec _ IdemOpAttr = showString "idem"

data OpAttr = OpBinAttr OpBinAttr | UnitOpAttr Term

unitStr = "unit"

instance Show OpAttr where
     showsPrec _ (OpBinAttr a) = shows a
     showsPrec _ (UnitOpAttr t) = showSignStr unitStr . shows t
     showList = showString . concat . map (\a -> ',' : show a)

data Class = TypUniverse | DownSet Type | ClassName Id

data TypeVarDecl = TypeVarDecl [Id] [Class] [Pos] -- commas, sep, commas

data TypeSheme = TypeSheme [TypeVarDecl] Type [Pos] -- "forall", commas, dot

data OpItem = OpDecl [OpId] TypeSheme [OpAttr] [Pos]
	    | OpDefn OpId TypeSheme Term [Pos] 
	    | OpRecDefn OpId TypeSheme Term [Pos] 
	    | AnnotatedOpItem OpItem [Anno]

data Component = Component Decl deriving (Show)      

-- full function type (in Decl) of constructor 
data Alternative = Construct Decl [Component] 
		 | Subsorts [TypeId]
		   deriving (Show) 

data DatatypeDecl = DatatypeDecl TypeId [Alternative] deriving (Show)    

class Annotatable a where
    annotate :: a -> [Anno] -> a

instance Annotatable OpItem where
    annotate (AnnotatedOpItem s _) l = AnnotatedOpItem s l
    annotate s l = AnnotatedOpItem s l

instance Annotatable SortItem where
    annotate (AnnotatedSortItem s _) l = AnnotatedSortItem s l
    annotate s l = AnnotatedSortItem s l

commaSortDecl :: TypeId -> Parser SortItem
commaSortDecl s = do { c <- comma 
		     ; (l, p) <- sortId `separatedBy` comma
		     ; let l' = s : l 
		           p' = tokPos c : map tokPos p
		       in
		       do { (t, q) <- subSortDecl
			  ; return (SubsortDecl l' t (p' ++ [q]))
			  }
		       <|> return (SortDecl l' p')
		     }

isoDecl :: TypeId -> Parser SortItem
isoDecl s = do { e <- equal
               ; subSortDefn (s, e)
		 <|>
		 (do { (l, p) <- sortId `separatedBy` equal
		     ; return (IsoDecl (s:l) (tokPos e : map tokPos p))
		     })
	       }

subSortDefn :: (TypeId, Token) -> Parser SortItem
subSortDefn (s, e) = 
    do { o <- oBrace
       ; v <- varId
       ; c <- colon 
       ; t <- funType
       ; d <- dot <|> bar	 
       ; f <- parseTerm
       ; p <- cBrace
       ; let decl = Decl [v] t [tokPos c]
	 in return (SubsortDefn s decl f 
		    (tokPos e:tokPos o:tokPos d:[tokPos p]))
       }

subSortDecl :: Parser (Type, Pos)
subSortDecl = do { l <- lessSign 
		   ; t <- funType
		   ; return (t, tokPos l)
		   }

sortItem :: Parser SortItem
sortItem = do { s <- sortId
	      ; do { (t, p) <- subSortDecl
		   ; return (SubsortDecl [s] t [p])
		   }
		<|>
		commaSortDecl s
		<|>
                isoDecl s
		<|> 
		return (SortDecl [s] [])
	      } 		

sortItems = do { key <- pluralKeyword sortStr
	       ; l <- itemAux sortItem
	       ; return (SortItems l [tokPos key])
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
