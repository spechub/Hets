
{- HetCATS/CASL/SortItem.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse SORT-ITEM and "sort/sorts SORT-ITEM ; ... ; SORT-ITEM"

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module SortItem where

import Id
import Keywords (lessS, sortS)
import Lexer
import AS_Basic_CASL
import AS_Annotation
import Anno_Parser
import Maybe
import Parsec
import Token
import Formula
import ItemAux

lessT = asKey lessS

commaSortDecl :: Id -> GenParser Char st SORT_ITEM
commaSortDecl s = do { c <- commaT 
		     ; (is, cs) <- sortId `separatedBy` commaT
		     ; let l = s : is 
		           p = tokPos c : map tokPos cs
		       in
		       subSortDecl (l, p)
		       <|> return (Sort_decl l p)
		     }

isoDecl :: Id -> GenParser Char st SORT_ITEM
isoDecl s = do { e <- equalT
               ; subSortDefn (s, tokPos e)
		 <|>
		 (do { (l, p) <- sortId `separatedBy` equalT
		     ; return (Iso_decl (s:l) (tokPos e : map tokPos p))
		     })
	       }

subSortDefn :: (Id, Pos) -> GenParser Char st SORT_ITEM
subSortDefn (s, e) = do { a <- annotations
			; o <- oBraceT
			; v <- varId
			; c <- colonT
			; t <- sortId
			; d <- dotT -- or bar
			; f <- formula
			; p <- cBraceT
			; return (Subsort_defn s v t (Annoted f [] a []) 
				  (e:tokPos o:tokPos c:tokPos d:[tokPos p]))
			}

subSortDecl :: ([Id], [Pos]) -> GenParser Char st SORT_ITEM
subSortDecl (l, p) = do { t <- lessT
		   ; s <- sortId
		   ; return (Subsort_decl l s (p++[tokPos t]))
		   }

sortItem :: GenParser Char st SORT_ITEM 
sortItem = do { s <- sortId ;
		    subSortDecl ([s],[])
		    <|>
		    commaSortDecl s
		    <|>
                    isoDecl s
		    <|> 
		    return (Sort_decl [s] [])
		  } 		

sortItems = do { p <- pluralKeyword sortS
	       ; a <- annotations
	       ; (v:vs, ts, b:ans) <- itemAux sortItem
	       ; let s = Annoted v [] a b
		     r = zipWith (\ x y -> Annoted x [] [] y) vs ans 
		 in return (Sort_items (s:r) (map tokPos (p:ts)))
	       }



