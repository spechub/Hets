module ParseType where

import Id (Token(Token), Id(Id), showTok) 
import Lexer ((<++>), (<<), keySign, toKey, checkWith)
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

isMixIdOrCross (Id ts cs) = 
    not (null (tail ts)) || 
	show ts `elem` ["<", productSign, altProductSign]

isPartialColon t = showTok t == colonChar : partialSuffix 

sortId = parseId  `checkWith` (not . isMixIdOrCross)

typeId c = do { i <- sortId
	      ; if isPartialColon c then 
		return (PartialType i) 
		else return (Type i [])
	      }

primType :: Token -> Parser Type
primType c = typeId c 
	   <|> (do { o <- oParen
		   ; (cParen >> return (crossProduct []))
		     <|> (funType o << cParen)
		   })

cross = makeToken(toKey productSign <|> toKey altProductSign <?> "cross")

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

parseType = funType (Token (":", nullPos))