
{- HetCATS/CASL/ItemList.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   generically parse "<keyword>/<keywords> ITEM ; ... ; ITEM"
-}

module ItemList where

import Id
import Keywords
import Lexer
import AS_Annotation
import Anno_Parser(annotationL)
import Maybe
import Parsec
import Token
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

