module SortItem where

import Id
import Lexer
import AS_Basic_CASL
import AS_Annotation
import Maybe
import Parsec
import Token
import Formula


less = asKey lessStr
equal = asKey equalStr
colon = asKey [colonChar]

commaSortDecl :: Id -> Parser SORT_ITEM
commaSortDecl s = do { c <- comma 
		     ; (is, cs) <- sortId `separatedBy` comma
		     ; let l = s : is 
		           p = tokPos c : map tokPos cs
		       in
		       subSortDecl (l, p)
		       <|> return (Sort_decl l p)
		     }

isoDecl :: Id -> Parser SORT_ITEM
isoDecl s = do { e <- equal
               ; subSortDefn (s, tokPos e)
		 <|>
		 (do { (l, p) <- sortId `separatedBy` equal
		     ; return (Iso_decl (s:l) (tokPos e : map tokPos p))
		     })
	       }

subSortDefn :: (Id, Pos) -> Parser SORT_ITEM
subSortDefn (s, e) = do { o <- oBrace
			; v <- varId
			; c <- colon
			; t <- sortId
			; d <- dot -- or bar
			; f <- formula
			; p <- cBrace
			; return (Subsort_defn s v t (Annoted f [] [] []) 
				  (e:tokPos o:tokPos c:tokPos d:[tokPos p]))
			}

subSortDecl :: ([Id], [Pos]) -> Parser SORT_ITEM
subSortDecl (l, p) = do { t <- less
		   ; s <- sortId
		   ; return (Subsort_decl l s (p++[tokPos t]))
		   }

sortItem :: Parser SORT_ITEM 
sortItem = do { s <- sortId ;
		    subSortDecl ([s],[])
		    <|>
		    commaSortDecl s
		    <|>
                    isoDecl s
		    <|> 
		    return (Sort_decl [s] [])
		  } 		










