
{- HetCATS/CASL/SortItem.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse SORT-ITEM and "sort/sorts SORT-ITEM ; ... ; SORT-ITEM"

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module CASL.SortItem where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import Common.Lib.Parsec
import Common.Token
import CASL.Formula
import CASL.ItemList

-- ------------------------------------------------------------------------
-- sortItem
-- ------------------------------------------------------------------------

commaSortDecl :: Id -> AParser SORT_ITEM
commaSortDecl s = do c <- anComma
		     (is, cs) <- sortId `separatedBy` anComma
		     let l = s : is 
		         p = tokPos c : map tokPos cs in
		       subSortDecl (l, p) <|> return (Sort_decl l p)

isoDecl :: Id -> AParser SORT_ITEM
isoDecl s = do e <- equalT
               subSortDefn (s, tokPos e)
		 <|>
		 (do (l, p) <- sortId `separatedBy` equalT
		     return (Iso_decl (s:l) (tokPos e : map tokPos p)))

subSortDefn :: (Id, Pos) -> AParser SORT_ITEM
subSortDefn (s, e) = do a <- annos
			o <- oBraceT
			v <- varId
			c <- colonT
			t <- sortId
			d <- dotT -- or bar
			f <- formula
			p <- cBraceT
			return (Subsort_defn s v t (Annoted f [] a []) 
				(e:tokPos o:tokPos c:tokPos d:[tokPos p]))

subSortDecl :: ([Id], [Pos]) -> AParser SORT_ITEM
subSortDecl (l, p) = do t <- lessT
			s <- sortId
			return (Subsort_decl l s (p++[tokPos t]))

sortItem :: AParser SORT_ITEM 
sortItem = do s <- sortId ;
	      subSortDecl ([s],[])
		    <|>
		    commaSortDecl s
		    <|>
                    isoDecl s
		    <|> 
		    return (Sort_decl [s] [])

sortItems :: AParser SIG_ITEMS
sortItems = itemList sortS sortItem Sort_items

