module ParseTerm where

import Id (Token(Token), Id(Id))
import Lexer (scanFloat, scanString, single)
import Parsec
import ParseType
import Token
import Term
import Type

-- ----------------------------------------------
-- parse decls (of bindings)
-- ----------------------------------------------

varId = parseId

colon = skipChar ':'

makeDecl t []  = []
makeDecl t ((c,v):l) = (Decl (Symb v t) c []) : (makeDecl t l)

varDecl :: Token -> Parser [Decl]
varDecl t = do { l <- separatedBy (const varId) comma t
	       ; r <- colon >>= funType
	       ; return (makeDecl r l)
 	       }

semi = skipChar ';'

varDecls :: Token -> Parser [Decl]
varDecls t = fmap (concat . map snd) (separatedBy varDecl semi t)

-- ----------------------------------------------
-- no-bracket-token, literal or place (for terms)
-- ----------------------------------------------
equal = skipChar '='

exEqual = makeToken (string "=e=") 
asTok = makeToken (string "as")
inTok = makeToken (string "in")


simpleTerm = fmap toQualId (makeToken(scanFloat <|> scanString <|>
				 otherToken <|> scanTermWords <|>
				 scanTermSigns) 
		       <|> uu)

mixTerm = parenTerm <|> simpleTerm

unknown :: Type
unknown = Type (simpleId "%%UNKNOWN\n") []

toQualId :: Token -> Term
toQualId t = BaseName (QualId (Symb (toId t) unknown) 0 Inferred)

terms :: Token -> Parser [Term]
terms t = do { l <- separatedBy (const mixTerm) comma t
	     ; return (map snd l)
	     }
 
varStr = "var"
opStr = "op"
predStr = "pred"

qualName = do { w <- string varStr <|> string opStr <|> string predStr
	      ; i <- parseId
	      ; t <- colon >>= funType
	      ; let ty = if w == predStr then predicate t else t 
		    l = if w == varStr then 1 else 0 
		in return (BaseName (QualId (Symb i ty) l UserGiven))
	      }

parenTerm = do { o <- oParen
               ; l <- single qualName <|> terms o
	       ; c <- cParen 
	       ; return (Application (toQualId o) l [c]) 
	       }

braceTerm = do { o <- oBrace
	       ; l <- option [] (terms o)
	       ; c <- cBrace
	       ; return (Application (toQualId o) l [c]) 
	       }



-- term = oParen >>= 





