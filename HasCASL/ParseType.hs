module ParseType where

import Id (Token(Token), Id(Id), showTok) 
import Lexer ((<++>), (<<), keySign, keyWord, signChars, checkWith)
import Parsec
import Token (skipChar, makeToken, parseId)
import Type

oParen = skipChar '('
cParen = skipChar ')'

separatedBy :: Parser a -> Parser Token -> Parser ([a], [Token])

separatedBy p s = do { r <- p
		     ; option ([r], []) 
		       (do { t <- s
			   ; (es, ts) <- separatedBy p s
			   ; return (r:es, t:ts)
			   })
		     }

toKey s = makeToken (let p = string s in 
		     if last s `elem` signChars then keySign p 
		     else keyWord p)

equalStr = "="
lessStr = "<"
lessSign = toKey lessStr

isSimpleTypeId (Id ts cs) = 
    null (tail ts) && 
	show ts `notElem` 
	  [equalStr, lessStr, totalFunArrow, partialFunArrow, productSign, altProductSign]

sortId = parseId  `checkWith` isSimpleTypeId

typeId = do { i <- sortId
	    ; return (Type i [])
	    }

primType :: Parser Type
primType = typeId 
	   <|> (do { o <- oParen
		   ; (cParen >> return (crossProduct []))
		     <|> (funType << cParen)
		   })

cross = toKey productSign <|> toKey altProductSign <?> "cross"

toId :: Token -> Id
toId i = Id [i] []

productType :: Parser Type
productType = fmap makeProduct (separatedBy primType cross)
    where makeProduct ([x], []) = x
	  makeProduct ([x, y], [c]) = Type (toId c) [x, y]
	  makeProduct ((x:l), (_:r)) = 
	      let Type c m = makeProduct (l, r) in Type c (x:m) 

arrow = makeToken (keySign (string totalFunArrow 
			    <++> option "" (string partialSuffix)))

funType :: Parser Type
funType = fmap makeFuns (separatedBy productType arrow)
    where makeFuns ([x], []) = x
	  makeFuns ((x:l), (c:r)) = 
	      let t = makeFuns (l, r) in Type (toId c) [x, t]

parseType = funType