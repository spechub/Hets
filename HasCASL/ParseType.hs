module ParseType where

import Id (Token(Token), Id(Id), showTok) 
import Lexer ((<++>), (<<), keySign, keyWord, signChars, checkWith)
import Parsec
import Token (skipChar, makeToken, parseId)
import Type

oParen = skipChar '('
cParen = skipChar ')'

separatedBy :: (Token -> Parser a) -> Parser Token 
	    -> Token -> Parser [(Token, a)]
separatedBy p s t = do { r <- p t
		       ; l <- option [] (s >>= separatedBy p s)
		       ; return ((t, r) : l) 
		       }

toKey s = makeToken (let p = string s in 
		     if last s `elem` signChars then keySign p 
		     else keyWord p)

lessStr = "<"
lessSign = toKey lessStr

isMixIdOrCross (Id ts cs) = 
    not (null (tail ts)) || 
	show ts `elem` [lessStr, productSign, altProductSign]

sortId = parseId  `checkWith` (not . isMixIdOrCross)

typeId _ = do { i <- sortId
	      ; return (Type i [])
	      }

primType :: Token -> Parser Type
primType c = typeId c 
	   <|> (do { o <- oParen
		   ; (cParen >> return (crossProduct []))
		     <|> (funType o << cParen)
		   })

cross = toKey productSign <|> toKey altProductSign <?> "cross"

toId :: Token -> Id
toId i = Id [i] []

productType :: Token -> Parser Type
productType c = fmap makeProduct (separatedBy primType cross c)
    where makeProduct [(c, x)] = x
	  makeProduct [(_, x), (c, y)] = Type (toId c) [x, y]
	  makeProduct ((_, x) : l@(_ : _)) =  
	      let Type c m = makeProduct l in Type c (x:m) 

arrow = makeToken (keySign (string totalFunArrow 
			    <++> option "" (string partialSuffix)))

funType :: Token -> Parser Type
funType c = fmap makeFuns (separatedBy productType arrow c)
    where makeFuns [(_, x)] = x
	  makeFuns ((_, x) : s@((c, _):_)) = 
	      let t = makeFuns s in Type (toId c) [x, t]

parseType = funType (Token [colonChar] nullPos)