
{- HetCATS/CASL/ItemAux.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse a list of items separated by semicolons (or dots) including annotations 
   The leading keyword may be singular or plural

   CASL-Summary
   Draft from 8 April 2002 
   C.5 Comments and Annotations
-}

module ItemAux where

import Id(Token())
import Keywords
import Lexer
import Token
import Parsec
import AS_Annotation
import Anno_Parser

pluralKeyword s = makeToken (keyWord (string s <++> option "" (string "s")))

optSemi :: GenParser Char st (Maybe Token, [Annotation])
optSemi = bind (\ x y -> (x, y)) (option Nothing (fmap Just semiT)) annotations

isStartKeyword s = s `elem` "":dotS:cDot:casl_reserved_words

lookAheadItemKeyword :: GenParser Char st ()
lookAheadItemKeyword = 
    do { c <- lookAhead (many1 scanLPD <|> many (oneOf signChars))
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
