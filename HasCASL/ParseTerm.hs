module ParseTerm where

import Id -- (Token(Token), Id(Id), showTok)
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

colon = toKey [colonChar]
partialColon = makeToken (keySign 
		    (char colonChar <:> option "" (string partialSuffix)))

varDecl :: Parser Decl
varDecl = do { (is, cs) <- separatedBy varId comma 
	     ; c <- colon 
	     ; t <- funType
	     ; return (Decl is t (map tokPos (cs ++ [c])))
 	     }

varDecls :: Parser ([Decl], [Pos])
varDecls = do { (ds, cs) <- separatedBy varDecl semi
	      ; return (ds, map tokPos cs)
	      }

parseDecls = varDecls
-- ----------------------------------------------
-- no-bracket-token, literal or place (for terms)
-- ----------------------------------------------
exEqual = string "=e="

keyword :: Show a => a -> Parser (a, Pos) 
keyword a = do {t <- toKey (show a)
		  ; return (a, tokPos t)
		  }

asOp = keyword AsType 
inOp = keyword InType
ofOp = keyword OfType

simpleTerm :: Parser Term
simpleTerm = fmap SimpleTerm (makeToken(scanFloat <|> scanString <|>
				 otherToken <|> scanTermWords <|>
				 try exEqual <|> scanTermSigns) 
		       <|> uu <?> "id/literal")

startTerm :: Parser Term
startTerm = parenTerm <|> braceTerm <|> sBrktTerm <|> simpleTerm

restTerm :: Parser Term
restTerm = startTerm <|> typedTerm

mixTerm = do { l <- startTerm <:> many restTerm <++> option [] (single quantTerm)
	     ; if length l == 1 then return (head l) 
	       else return (MixTerm l)
	     } <|> quantTerm  

typedTerm :: Parser Term
typedTerm = do { (c, p) <- try (ofOp <|> asOp <|> inOp) <?> "type"
	       ; t <- funType
	       ; return (TypeInfo c t [p])
	       }


terms :: Parser ([Term], [Pos])
terms = do { (ts, ps) <- separatedBy mixTerm comma
	   ; return (ts, map tokPos ps)
	   }

isColon c = showTok c == [colonChar]

parsePartialType c = if isColon c then funType else fmap PartialType sortId

qualName = do { (w, p) <- try (keyword VarQ <|> keyword OpQ <|> keyword PredQ) 
		      <?> "qualifier"
	      ; i <- parseId
	      ; c <- partialColon `checkWith` \c -> w == OpQ
		                              || showTok c == [colonChar]
	      ; t <- parsePartialType c
	      ; return (Qualified (QualId w i t [p, tokPos c]))
	      }

parenTerm = do { o <- oParen
               ; (ts, ps) <- fmap (\t -> ([t], [])) qualName <|> terms
	       ; c <- cParen 
	       ; return (Application Parens ts (tokPos o : ps ++ [tokPos c]))
	       }

braceTerm = do { o <- oBrace
               ; (ts, ps) <- option ([], []) terms
	       ; c <- cBrace 
	       ; return (Application Braces ts (tokPos o : ps ++ [tokPos c]))
	       }

sBrktTerm = do { o <- opBrkt
               ; (ts, ps) <- option ([], []) terms
	       ; c <- clBrkt 
	       ; return (Application Squares ts (tokPos o : ps ++ [tokPos c]))
	       }

quant = try (keyword ExistsUnique <|> keyword Exists <|> keyword Forall 
	<|> keyword LambdaPartial) <?> "quantifier"

getDot = makeToken (keySign (oneOf (dotChar:middleDotStr) 
			     <:> option "" (string totalSuffix)))

isLambda (LambdaPartial) = True
isLambda (LambdaTotal) = True
isLambda _ = False

quantTerm = do { (q, p) <- quant
	       ; (vs, ps) <- varDecls
	       ; d <- getDot `checkWith`  \d -> length (showTok d) == 1 
		                                || isLambda q 
               ; t <- mixTerm
               ; let qu = if length (showTok d) > 1 then LambdaTotal else q
	         in  return (Binding qu vs t (p:ps ++ [tokPos d]))
	       }

parseTerm = mixTerm
