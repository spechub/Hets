
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
import Anno_Parser(annotationL)
import Maybe
import Parsec
import Token
import Formula
import List(delete)

-- ----------------------------------------------
-- annotations
-- ----------------------------------------------

-- skip to leading annotation and read many
annos :: GenParser Char st [Annotation]
annos = skip >> many (annotationL << skip)

-- annotations on one line
lineAnnos :: GenParser Char st [Annotation]
lineAnnos = do p <- getPosition
	       do a <- annotationL  
		  skip
		  q <- getPosition
		  if sourceLine q == sourceLine p then
		      do l <- lineAnnos
			 return (a:l)
		      else return [a]
		 <|> return []

-- optional semicolon followed by annotations on the same line
optSemi :: GenParser Char st (Maybe Token, [Annotation])
optSemi = bind (,) (option Nothing (fmap Just semiT)) lineAnnos

-- succeeds if an item is not continued after a semicolon
tryItemEnd :: [String] -> GenParser Char st ()
tryItemEnd l = 
    try (do c <- lookAhead (annos >> 
			      (single (oneOf "\"([{")
			       <|> placeS
			       <|> scanAnySigns
			       <|> many scanLPD))
	    if null c || c `elem` l then return () else unexpected c)


-- remove quantifier exists from casl_reserved_word 
-- because it may start a formula in "axiom/axioms ... \;"
startKeyword :: [String]
startKeyword = dotS:cDot:
		   (delete existsS casl_reserved_words)

annoParser :: GenParser Char st a -> GenParser Char st (Annoted a)
annoParser parser = bind (\x y -> Annoted y [] x []) annos parser

itemList :: String -> GenParser Char st b
               -> ([Annoted b] -> [Pos] -> a) -> GenParser Char st a

itemList keyword parser constr =
    do p <- pluralKeyword keyword
       (vs, ts, ans) <- itemAux (annoParser parser)
       let r = zipWith appendAnno vs ans in 
	   return (constr r (map tokPos (p:ts)))

appendAnno :: Annoted a -> [Annotation] -> Annoted a
appendAnno (Annoted x p l r) y = Annoted x p l (r++y)

itemAux :: GenParser Char st a 
	-> GenParser Char st ([a], [Token], [[Annotation]])
itemAux itemParser = 
    do a <- itemParser
       (m, an) <- optSemi
       case m of Nothing -> return ([a], [], [an])
                 Just t -> do tryItemEnd startKeyword
			      return ([a], [t], [an])
	                   <|> 
	                   do (as, ts, ans) <- itemAux itemParser
			      return (a:as, t:ts, an:ans)

-- ------------------------------------------------------------------------
-- sortItem
-- ------------------------------------------------------------------------

lessT :: GenParser Char st Token
lessT = asKey lessS

commaSortDecl :: Id -> GenParser Char st SORT_ITEM
commaSortDecl s = do c <- commaT 
		     (is, cs) <- sortId `separatedBy` commaT
		     let l = s : is 
		         p = tokPos c : map tokPos cs in
		       subSortDecl (l, p) <|> return (Sort_decl l p)

isoDecl :: Id -> GenParser Char st SORT_ITEM
isoDecl s = do e <- equalT
               subSortDefn (s, tokPos e)
		 <|>
		 (do (l, p) <- sortId `separatedBy` equalT
		     return (Iso_decl (s:l) (tokPos e : map tokPos p)))

subSortDefn :: (Id, Pos) -> GenParser Char st SORT_ITEM
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

subSortDecl :: ([Id], [Pos]) -> GenParser Char st SORT_ITEM
subSortDecl (l, p) = do t <- lessT
			s <- sortId
			return (Subsort_decl l s (p++[tokPos t]))

sortItem :: GenParser Char st SORT_ITEM 
sortItem = do s <- sortId ;
	      subSortDecl ([s],[])
		    <|>
		    commaSortDecl s
		    <|>
                    isoDecl s
		    <|> 
		    return (Sort_decl [s] [])

sortItems :: GenParser Char st SIG_ITEMS
sortItems = itemList sortS sortItem Sort_items

