module Formula where

import Id
import Lexer
import Token
import AS_Basic_CASL
import Parsec

varStr = "var"
predStr = "pred"
opStr = "op"
exStr = "exists"
allStr = "forall"
middleDotStr = "\183"
dotChar = '.'

equal = asKey equalStr
colon = asKey [colonChar]
semi = asKey ";"

dot = try(asKey [dotChar] <|> asKey middleDotStr) <?> "dot"
cross = try(asKey productSign <|> asKey altProductSign) <?> "cross"

simpleTerm :: GenParser Char st TERM
simpleTerm = fmap Mixfix_token (makeToken(scanFloat <|> scanString 
		       <|>  scanQuotedChar <|> scanDotWords <|> scanWords 
		       <|>  scanSigns <|> string place <?> "id/literal" )) 


startTerm :: GenParser Char st TERM
startTerm = parenTerm <|> braceTerm <|> sBrktTerm <|> simpleTerm

restTerm :: GenParser Char st TERM
restTerm = startTerm <|> typedTerm <|> castedTerm

mixTerm = do { l <- startTerm <:> many restTerm
             ; if length l == 1 then return (head l) 
               else return (Mixfix_term l)
             } 

whenTerm = do { t <- mixTerm 
	      ; do { w <- asKey "when"
		   ;	f <- formula
		   ; e <- asKey "else"
		   ; r <- whenTerm
		   ; return (Conditional t f r [tokPos w, tokPos e])
		   }
		<|> return t
	      }

term = whenTerm

typedTerm :: GenParser Char st TERM
typedTerm = do { c <- colon
               ; t <- sortId
               ; return (Mixfix_sorted_term t [tokPos c])
               }

castedTerm :: GenParser Char st TERM
castedTerm = do { c <- asKey "as"
		; t <- sortId
		; return (Mixfix_cast t [tokPos c])
		}

terms :: GenParser Char st ([TERM], [Pos])
terms = do { (ts, ps) <- term `separatedBy` comma
           ; return (ts, map tokPos ps)
           }

oParen = sepChar '('
cParen = sepChar ')'

qualVarName o = do { v <- asKey varStr
		   ; i <- varId
		   ; c <- colon 
		   ; s <- sortId
		   ; p <- cParen
		   ; return (Qual_var i s [o, tokPos v, tokPos c, tokPos p])
		   }

qualOpName o = do { v <- asKey opStr
		  ; i <- parseId
		  ; c <- sepChar colonChar 
		  ; do { q <- asKey partialSuffix 
		       ; s <- sortId
		       ; p <- cParen
		       ; return (Application 
				 (Qual_op_name i 
				  (Partial_op_type [] s [tokPos q]) 
				  [tokPos v, tokPos c, tokPos p]) [] [])
		       }
		    <|> do { t <- opType 
			   ; p <- cParen
			   ; return (Application 
				     (Qual_op_name i t
				      [tokPos v, tokPos c, tokPos p]) [] [])
			   }
		   }

opType = do { (ts, ps) <- sortId `separatedBy` cross
	    ; do { a <- makeToken (string totalFunArrow)
		 ; let qs = map tokPos ps ++[tokPos a] 
		   in
		   do { asKey partialSuffix
		      ; s <- sortId
		      ; return (Partial_op_type ts s qs)
		      } <|> do { s <- sortId
			       ; return (Total_op_type ts s qs)
			       }
		   } <|> (if length ts == 1 then return 
	                    (Total_op_type [] (head ts) [])
	                  else unexpected ("missing " ++ totalFunArrow))
	    }

parenTerm = do { o <- oParen
               ; qualVarName (tokPos o) 
		 <|> qualOpName (tokPos o)
		 <|> do { (ts, ps) <- terms
		        ; c <- cParen
		        ; return (Mixfix_parenthesized ts 
				  (tokPos o : ps ++ [tokPos c]))
			}
	       }

braceTerm = do { o <- oBrace
               ; (ts, ps) <- option ([], []) terms
               ; c <- cBrace 
               ; return (Mixfix_braced ts (tokPos o : ps ++ [tokPos c]))
               }

sBrktTerm = do { o <- opBrkt
               ; (ts, ps) <- option ([], []) terms
               ; c <- clBrkt 
               ; return (Mixfix_bracketed ts (tokPos o : ps ++ [tokPos c]))
               }

quant = try(
        do { q <- asKey (exStr++"!")
	   ; return (Unique_existential, tokPos q)
	   }
        <|>
        do { q <- asKey exStr
	   ; return (Existential, tokPos q)
	   }
        <|>
        do { q <- asKey allStr
	   ; return (Universal, tokPos q)
	   })
        <?> "quantifier"
       
quantFormula = do { (q, p) <- quant
		  ; (vs, ps) <- varDecl `separatedBy` semi
		  ; d <- dot
		  ; f <- formula
		  ; return (Quantification q vs f
			    (p: map tokPos ps ++[tokPos d]))
		  }

varDecl = do { (vs, ps) <- varId `separatedBy` comma
	     ; c <- colon
	     ; s <- sortId
	     ; return (Var_decl vs s (map tokPos ps ++[tokPos c]))
	     }

updFormulaPos _ _ f = f

predType = do { (ts, ps) <- sortId `separatedBy` cross
	      ; return (Pred_type ts (map tokPos ps))
	      } <|> do { o <- oParen
		       ; c <- cParen
		       ; return (Pred_type [] [tokPos o, tokPos c])
		       }

qualPredName o = do { v <- asKey predStr
		    ; i <- parseId
		    ; c <- colon 
		    ; s <- predType
		    ; p <- cParen
		    ; return (Predication 
			      (Qual_pred_name i s 
			       [o, tokPos v, tokPos c, tokPos p]) [] [])
		    }

parenFormula = do { o <- oParen
		  ; qualPredName (tokPos o) 
		    <|> do { f <- formula
			   ; c <- cParen
		           ; return (updFormulaPos (tokPos o) (tokPos c) f)
			   }
		  }

termFormula = do { t <- term
		 ; do { e <- asKey "=e="
		      ; r <- term 
		      ; return (Existl_equation t r [tokPos e])
		      }
                   <|>
		   do { e <- equal
		      ; r <- term 
		      ; return (Strong_equation t r [tokPos e])
		      }
                   <|>
		   do { e <- asKey "in"
		      ; s <- sortId 
		      ; return (Membership t s [tokPos e])
		      }
		   <|> return (Mixfix_formula t)
		   }

primFormula = do { c <- asKey "true"
		 ; return (True_atom [tokPos c])
		 }
              <|>
	      do { c <- asKey "false"
		 ; return (False_atom [tokPos c])
		 }
              <|>
	      do { c <- asKey "def"
		 ; t <- term
		 ; return (Definedness t [tokPos c])
		 }
              <|>
	      do { c <- asKey "not" <|> asKey "\172"
		 ; f <- primFormula 
		 ; return (Negation f [tokPos c])
		 }
              <|> parenFormula <|> quantFormula <|> termFormula

andKey = asKey "/\\"
orKey = asKey "\\/"

andOrFormula = do { f <- primFormula
		  ; do { c <- andKey
		       ; (fs, ps) <- primFormula `separatedBy` andKey
		       ; return (Conjunction (f:fs) (map tokPos (c:ps)))
		       }
		    <|>
		    do { c <- orKey
		       ; (fs, ps) <- primFormula `separatedBy` orKey
		       ; return (Disjunction (f:fs) (map tokPos (c:ps)))
		       }
		    <|> return f
		  }
implKey = asKey "=>"
ifKey = asKey "if"

impFormula = do { f <- andOrFormula
		  ; do { c <- implKey
		       ; (fs, ps) <- andOrFormula `separatedBy` implKey
		       ; return (makeImpl (f:fs) (map tokPos (c:ps)))
		       }
		    <|>
		    do { c <- ifKey
		       ; (fs, ps) <- andOrFormula `separatedBy` ifKey
		       ; return (makeIf (f:fs) (map tokPos (c:ps)))
		       }
		    <|>
		    do { c <- asKey "<=>"
		       ; g <- andOrFormula
		       ; return (Equivalence f g [tokPos c])
		       }
		    <|> return f
		  }
		    where makeImpl [f,g] p = Implication f g p
		          makeImpl (f:r) (c:p) = 
			             Implication f (makeImpl r p) [c]
			  makeIf l p = makeImpl (reverse l) (reverse p)

formula = impFormula
