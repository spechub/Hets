
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
import Keywords
import Lexer
import AS_Basic_CASL
import AS_Annotation
import Anno_Parser (comment, annote)
import Maybe
import Parsec
import Token
import Formula

pluralKeyword s = makeToken (keyWord (string s <++> option "" (string "s")))

-- following annotations
anno = 	comment <|> annote  -- position not included yet

lineAnnos = do { p <- getPosition
	       ; do { a <- anno  
		    ; skip
		    ; q <- getPosition
		    ; if sourceLine q == sourceLine p then
		      do { l <- lineAnnos
			 ; return (a:l)
			 }
		      else return [a]
		    }
		 <|> return []
	       }

optSemi :: GenParser Char st (Maybe Token, [Annotation])
optSemi = bind (,) (option Nothing (fmap Just semiT)) lineAnnos

-- skip to leading annotation and read it
annos = skip >> many (anno << skip)

-- remove quantifier exist from casl_reserved_word!
isStartKeyword s = s `elem` "}":"]":dotS:cDot:casl_reserved_words

lookAheadItemKeyword :: GenParser Char st ()
lookAheadItemKeyword = 
    do { c <- lookAhead (annos >> 
			 (many1 scanLPD <|> single (oneOf ("}]"++signChars))))
       ; if isStartKeyword c then return () else unexpected c
       }

itemAux :: GenParser Char st a 
	-> GenParser Char st ([a], [Token], [[Annotation]])
itemAux itemParser = 
    do { a <- itemParser
       ; (m, an) <- optSemi
       ; case m of { Nothing -> return ([a], [], [an])
                   ; Just t -> do { try lookAheadItemKeyword
				  ; return ([a], [t], [an])
				  }
	                        <|> 
	                        do { (as, ts, ans) <- itemAux itemParser
				   ; return (a:as, t:ts, an:ans)
				   }
		   }
       }

-- ------------------------------------------------------------------------
-- sortItem
-- ------------------------------------------------------------------------

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
subSortDefn (s, e) = do { a <- annos
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

appendAnno x y =  Annoted x [] [] y

sortItems = do { p <- pluralKeyword sortS
	       ; a <- annos
	       ; (v:vs, ts, b:ans) <- itemAux sortItem
	       ; let s = Annoted v [] a b
		     r = zipWith appendAnno vs ans 
		 in return (Sort_items (s:r) (map tokPos (p:ts)))
	       }



