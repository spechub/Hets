module ParseTerm where

import Id (Token(Token), Id(Id))
import Lexer ((<:>), (<++>), flat, scanFloat, scanString
	     , single, keyStr, keySign)
import Parsec
import ParseType
import Token
import Term
import Type

-- ----------------------------------------------
-- parse decls (of bindings)
-- ----------------------------------------------

varId = parseId

colon = makeToken (keySign (string [colonChar]))
partialColon = makeToken (char colonChar <:> option "" (string partialSuffix))

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
exEqual = string "=e="

asTok = makeToken (keyStr asStr)
inTok = makeToken (keyStr inStr)

simpleTerm :: Parser Term
simpleTerm = fmap toQualId (makeToken(scanFloat <|> scanString <|>
				 otherToken <|> scanTermWords <|>
				 try exEqual <|> scanTermSigns) 
		       <|> uu)

startTerm :: Parser Term
startTerm = parenTerm <|> braceTerm <|> brktTerm <|> simpleTerm

restTerm :: Parser Term
restTerm = startTerm <|> typedTerm

mixTerm = do { l <- startTerm <:> many restTerm 
	     ; if length l == 1 then return (head l) 
	       else return (Application MixTerm l [])
	     } <|> quantTerm  

typeOfPrefix t = if [colonChar] == show t then OfType
		 else if asStr == show t then AsType
		      else if inStr == show t then InType
			   else error ("typeOfPrefix: " ++ show t)

typedTerm :: Parser Term
typedTerm = do { c <- try (colon <|> asTok <|> inTok)
	       ; t <- funType c
	       ; return (Typed MixTerm (typeOfPrefix c) t) 
	       }

toQualId :: Token -> Term
toQualId t = BaseName (QualId (Symb (toId t) Unknown) 0 Inferred)

terms :: Token -> Parser [Term]
terms t = do { l <- separatedBy (const mixTerm) comma t
	     ; return (map snd l)
	     }

qualName = do { w <- try (makeToken 
			  (keyStr varStr <|> keyStr opStr <|> keyStr predStr))
	      ; i <- parseId
	      ; t <- colon >>= funType
	      ; let ty = if show w == predStr then predicate t else t 
		    l = if show w == varStr then 1 else 0 
		in return (BaseName (QualId (Symb i ty) l UserGiven))
	      }

parenTerm = do { o <- oParen
               ; l <- single qualName <|> terms o
	       ; c <- cParen 
	       ; if length l == 1 && isBaseName (head l) 
		 then return (head l) 
		 else return (Application MixTerm l [o,c]) 
	       }

braTerm op cl = do { o <- op
		   ; l <- option [] (terms o)
		   ; c <- cl
		   ; return (Application MixTerm l [o,c]) 
		   }

braceTerm = braTerm oBrace cBrace
brktTerm = braTerm opBrkt clBrkt

quant = keyStr allStr
	<|> (keyStr exStr <|> keyStr lamStr) 
		<++> option "" (string totalSuffix)

getDot = oneOf ".\183" <:> option "" (string totalSuffix)

binder t = if show t == allStr then Forall
	     else if show t == exStr then Exists
	          else if show t == exStr ++ totalSuffix then ExistsUnique
		       else if show t == lamStr then Lambda Partial
			    else if show t == lamStr ++ totalSuffix 
				 then Lambda Total
				 else error ("binder: " ++ show t)

isLambda (Lambda _) = True
isLambda _ = False

quantTerm = do { q <- try (makeToken quant)
	       ; v <- varDecls q
	       ; d <- makeToken getDot
               ; t <- mixTerm
	       ; let b = binder q
		     c = if isLambda b && [last (show d)] == totalSuffix
		         then Lambda Total else b
		 in return (Binding c v t)
	       }

parseTerm = mixTerm
