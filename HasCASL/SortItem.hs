module SortItem where

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


commaSortDecl :: [(Token, Id)] -> Parser ParsedSortItems
commaSortDecl l = do { c <- comma
		     ; s <- sortId
		     ; let l2 = (c, s) : l in
		       commaSortDecl l2
		       <|> subSortDecl l2
		       <|> return (AllLess l2 Nothing)
		     }
equalSortDecl :: Token -> [(Token, Id)] -> Parser [(Token, Id)]
equalSortDecl e l = do { s2 <- sortId
		       ; let l2 = (e, s2):l in
			 option l2 (do { e2 <- equal
				       ; equalSortDecl e2 l2
				       })
		       } 

equal = skipChar '='

isoDecl :: Token -> Id -> Parser ParsedSortItems
isoDecl key s1 = do { e <- equal
                    ; subSortDefn key s1
		      <|>
		      (do { l <- equalSortDecl e [(key, s1)]
			  ; return (AllEqual l)
			  })
		    }

subSortDefn :: Token -> Id -> Parser ParsedSortItems
subSortDefn key s = do { o <- oBrace
		       ; v <- varId
		       ; c <- colon
		       ; t <- funType c
		       ; dot <|> bar	 
		       ; e <- parseTerm
		       ; cBrace
		       ; let f = Binding SupersortVar [Decl (Symb v t) o []] e
			 in return (SubType (key, s) t f)
		       }

subSortDecl :: [(Token, Id)] -> Parser ParsedSortItems
subSortDecl l = do { t <- skipChar '<'
		   ; s <- sortId
		   ; return (AllLess l (Just (t, s)))
		   }

sortItem :: Token -> Parser ParsedSortItems
sortItem key = do { s1 <- sortId
		  ; subSortDecl [(key, s1)]
		    <|>
		    commaSortDecl [(key, s1)]
		    <|>
                    isoDecl key s1
		    <|> 
		    return (AllLess [(key, s1)] Nothing)
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

sortItems ast = do { key <- pluralKeyword "sort" 
		   ; itemAux sortItemAux ast key
		   }













