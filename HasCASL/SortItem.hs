module SortItem (sortItems) where

import Id
import ItemAux
import Lexer
import LocalEnv
import Maybe
import Parsec
import ParseTerm
import ParseType
import Token
import Term
import Type

data ParsedSortItems = AllLess [(Token, Id)] (Maybe (Token, Id)) 
		     | AllEqual [(Token, Id)] 
		     | SubType (Token, Id) Type Term 
		       deriving (Show)


commaSortDecl :: (Token, Id) -> Parser ParsedSortItems
commaSortDecl s = do { l <- comma >>= separatedBy (const sortId) comma
		     ; let l' = s : l in
		       subSortDecl l'
		       <|> return (AllLess l' Nothing)
		     }

isoDecl :: (Token, Id) -> Parser ParsedSortItems
isoDecl s = do { e <- equal
               ; subSortDefn s
		 <|>
		 (do { l <- separatedBy (const sortId) equal e
		     ; return (AllEqual (s:l))
		     })
	       }

subSortDefn :: (Token, Id) -> Parser ParsedSortItems
subSortDefn s = do { o <- oBrace
		   ; v <- varId
		   ; t <- colon >>= funType
		   ; dot <|> bar	 
		   ; e <- parseTerm
		   ; cBrace
		   ; let f = Binding SupersortVar [Decl (Symb v t) o []] e
		     in return (SubType s t f)
		   }

subSortDecl :: [(Token, Id)] -> Parser ParsedSortItems
subSortDecl l = do { t <- lessSign
		   ; s <- sortId
		   ; return (AllLess l (Just (t, s)))
		   }

sortItem :: Token -> Parser ParsedSortItems
sortItem key = do { s1 <- sortId
		  ; let s = (key, s1) in
		    subSortDecl [s]
		    <|>
		    commaSortDecl s
		    <|>
                    isoDecl s
		    <|> 
		    return (AllLess [s] Nothing)
		  } 		

toSymb s = Symb s Sort

mkItem :: [Type] -> [Type] -> (Token, Id) -> SortItem
mkItem subs supers (key, id) = 
    SortItem (Decl (toSymb id) key []) (SortRels subs supers) Nothing []

asSortItems :: ParsedSortItems -> [SortItem]
asSortItems (AllLess l m) = 
    let p = maybeToList m
        f = map (asType . snd)
	super = f p
	sis = map (mkItem [] super) l 
	subs = reverse (f l)
	supers = map (mkItem subs []) p
    in supers ++ sis 

asSortItems (AllEqual l) =
    let  types = reverse (map (asType . snd) l)
         sorts = map (mkItem types types) l 
    in   sorts -- maybe delete self

asSortItems (SubType p t e) =
    [(mkItem [] [t] p) {sortDef = Just (SubsortDefn e)}]

sortItemAux ast key = do { si <- sortItem key
			 ; return ((map ASortItem (asSortItems si)) ++ ast)
			 }

sortItems ast = do { key <- pluralKeyword sortStr
		   ; itemAux sortItemAux ast key
		   }










