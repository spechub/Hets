module ParseTerm where

import Id (Token(Token), Id(Id), showTok)
import Lexer -- ((<:>), (<++>), flat, scanFloat, scanString, single, toKey)
import Parsec
import ParseType
import Token
import Term
import Type

-- ----------------------------------------------
-- parse decls (of bindings)
-- ----------------------------------------------

varId = parseId

colon = makeToken (toKey [colonChar])
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

asTok = makeToken (toKey asStr)
inTok = makeToken (toKey inStr)

simpleTerm :: Parser Term
simpleTerm = fmap toQualId (makeToken(scanFloat <|> scanString <|>
				 otherToken <|> scanTermWords <|>
				 try exEqual <|> scanTermSigns) 
		       <|> uu <?> "id/literal")

startTerm :: Parser Term
startTerm = parenTerm <|> braceTerm <|> brktTerm <|> simpleTerm

restTerm :: Parser Term
restTerm = startTerm <|> typedTerm

mixTerm = do { l <- startTerm <:> many restTerm <++> option [] (single quantTerm)
	     ; if length l == 1 then return (head l) 
	       else return (Application MixTerm l [])
	     } <|> quantTerm  

typeOfPrefix t = if [colonChar] == show t then OfType
		 else if asStr == show t then AsType
		      else if inStr == show t then InType
			   else error ("typeOfPrefix: " ++ show t)

typedTerm :: Parser Term
typedTerm = do { c <- try (colon <|> asTok <|> inTok) <?> "type"
	       ; t <- funType c
	       ; return (Typed MixTerm (typeOfPrefix c) t) 
	       }

toQualId :: Token -> Term
toQualId t = BaseName (QualId (Symb (toId t) Unknown) 0 Inferred)

terms :: Token -> Parser [Term]
terms t = do { l <- separatedBy (const mixTerm) comma t
	     ; return (map snd l)
	     }

isPartialId (PartialType _) = True
isPartialId _ = False

qualName = do { w <- makeToken 
		     (toKey varStr <|> toKey opStr <|> toKey predStr)
	      ; i <- parseId
	      ; c <- partialColon `checkWith` \c -> showTok w == opStr
		|| not (isPartialColon c)
	      ; t <- funType c `checkWith` \t -> not (isPartialColon c) 
		||  isPartialId t
	      ; let s = showTok w 
		    ty = if s == predStr then predicate t else t 
		    l = if s == varStr then 1 else 0 
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

quant = toKey allStr
	<|> (toKey exStr <|> toKey lamStr) 
		<++> option "" (string totalSuffix) <?> "quantifier"

getDot = oneOf ".\183" <:> option "" (string totalSuffix)

binder t = let s = showTok t in
	   if s == allStr then Forall
	     else if s == exStr then Exists
	          else if s == exStr ++ totalSuffix then ExistsUnique
		       else if s == lamStr then Lambda Partial
			    else if s == lamStr ++ totalSuffix 
				 then Lambda Total
				 else error ("binder: " ++ s)

isLambda (Lambda _) = True
isLambda _ = False

quantTerm = do { q <- try (makeToken quant)
	       ; v <- varDecls q
	       ; d <- makeToken getDot `checkWith` \d -> length (showTok d) == 1
		 || isLambda (binder q) 
               ; t <- mixTerm
	       ; let b = binder q
		     c = if isLambda b && length (showTok d) > 1
		         then Lambda Total else b
		 in return (Binding c v t)
	       }

parseTerm = mixTerm
