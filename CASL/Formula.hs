module Formula where

import Id
import Keywords
import Lexer -- (separatedBy,(<:>),scanFloat,scanString)
import Token
-- import CaslLanguage
import AS_Basic_CASL
import Parsec


equalT = asKey equalS
colonT = asKey colonS
semiT = asKey semiS
oParenT = asKey oParenS
cParenT = asKey cParenS
quMarkT = asKey quMark

dotT = try(asKey dotS <|> asKey middleDotS) <?> "dot"
crossT = try(asKey prodS <|> asKey timesS) <?> "cross"

simpleTerm :: GenParser Char st TERM
simpleTerm = fmap Mixfix_token (makeToken(scanFloat <|> scanString 
		       <|>  scanQuotedChar <|> scanDotWords <|> scanWords 
		       <|>  scanSigns <|> string place <?> "id/literal" )) 


startTerm :: GenParser Char st TERM
startTerm = parenTerm <|> braceTerm <|> bracketTerm <|> simpleTerm

restTerm :: GenParser Char st TERM
restTerm = startTerm <|> typedTerm <|> castedTerm

mixTerm = do { l <- startTerm <:> many restTerm
             ; if length l == 1 then return (head l) 
               else return (Mixfix_term l)
             } 

whenTerm = do { t <- mixTerm 
	      ; do { w <- asKey whenS
		   ; f <- formula
		   ; e <- asKey elseS
		   ; r <- whenTerm
		   ; return (Conditional t f r [tokPos w, tokPos e])
		   }
		<|> return t
	      }

term = whenTerm

typedTerm :: GenParser Char st TERM
typedTerm = do { c <- colonT
               ; t <- sortId
               ; return (Mixfix_sorted_term t [tokPos c])
               }

castedTerm :: GenParser Char st TERM
castedTerm = do { c <- asKey asS
		; t <- sortId
		; return (Mixfix_cast t [tokPos c])
		}

terms :: GenParser Char st ([TERM], [Pos])
terms = do { (ts, ps) <- term `separatedBy` commaT
           ; return (ts, map tokPos ps)
           }


qualVarName o = do { v <- asKey varS
		   ; i <- varId
		   ; c <- colonT 
		   ; s <- sortId
		   ; p <- cParenT
		   ; return (Qual_var i s [o, tokPos v, tokPos c, tokPos p])
		   }

qualOpName o = do { v <- asKey opS
		  ; i <- parseId
		  ; c <- makeToken (string colonS) 
		  ; do { q <- quMarkT
		       ; s <- sortId
		       ; p <- cParenT
		       ; return (Application 
				 (Qual_op_name i 
				  (Partial_op_type [] s [tokPos q]) 
				  [tokPos v, tokPos c, tokPos p]) [] [])
		       }
		    <|> do { t <- opType 
			   ; p <- cParenT
			   ; return (Application 
				     (Qual_op_name i t
				      [tokPos v, tokPos c, tokPos p]) [] [])
			   }
		   }

opType = do { (ts, ps) <- sortId `separatedBy` crossT
	    ; do { a <- makeToken (string funS)
		 ; let qs = map tokPos ps ++[tokPos a] 
		   in
		   do { quMarkT
		      ; s <- sortId
		      ; return (Partial_op_type ts s qs)
		      } <|> do { s <- sortId
			       ; return (Total_op_type ts s qs)
			       }
		   } <|> (if length ts == 1 then return 
	                    (Total_op_type [] (head ts) [])
	                  else unexpected ("missing " ++ funS))
	    }

parenTerm = do { o <- oParenT
               ; qualVarName (tokPos o) 
		 <|> qualOpName (tokPos o)
		 <|> do { (ts, ps) <- terms
		        ; c <- cParenT
		        ; return (Mixfix_parenthesized ts 
				  (tokPos o : ps ++ [tokPos c]))
			}
	       }

braceTerm = do { o <- oBraceT
               ; (ts, ps) <- option ([], []) terms
               ; c <- cBraceT 
               ; return (Mixfix_braced ts (tokPos o : ps ++ [tokPos c]))
               }

bracketTerm = do { o <- oBracketT
		 ; (ts, ps) <- option ([], []) terms
		 ; c <- cBracketT 
		 ; return (Mixfix_bracketed ts (tokPos o : ps ++ [tokPos c]))
		 }

quant = try(
        do { q <- asKey (existsS++exMark)
	   ; return (Unique_existential, tokPos q)
	   }
        <|>
        do { q <- asKey existsS
	   ; return (Existential, tokPos q)
	   }
        <|>
        do { q <- asKey forallS
	   ; return (Universal, tokPos q)
	   })
        <?> "quantifier"
       
quantFormula = do { (q, p) <- quant
		  ; (vs, ps) <- varDecl `separatedBy` semiT
		  ; d <- dotT
		  ; f <- formula
		  ; return (Quantification q vs f
			    (p: map tokPos ps ++[tokPos d]))
		  }

varDecl = do { (vs, ps) <- varId `separatedBy` commaT
	     ; c <- colonT
	     ; s <- sortId
	     ; return (Var_decl vs s (map tokPos ps ++[tokPos c]))
	     }

-- to be implemented
updFormulaPos _ _ f = f  

predType = do { (ts, ps) <- sortId `separatedBy` crossT
	      ; return (Pred_type ts (map tokPos ps))
	      } <|> do { o <- oParenT
		       ; c <- cParenT
		       ; return (Pred_type [] [tokPos o, tokPos c])
		       }

qualPredName o = do { v <- asKey predS
		    ; i <- parseId
		    ; c <- colonT 
		    ; s <- predType
		    ; p <- cParenT
		    ; return (Predication 
			      (Qual_pred_name i s 
			       [o, tokPos v, tokPos c, tokPos p]) [] [])
		    }

parenFormula = do { o <- oParenT
		  ; qualPredName (tokPos o) 
		    <|> do { f <- formula
			   ; c <- cParenT
		           ; return (updFormulaPos (tokPos o) (tokPos c) f)
			   }
		  }

termFormula = do { t <- term
		 ; do { e <- asKey exEqual
		      ; r <- term 
		      ; return (Existl_equation t r [tokPos e])
		      }
                   <|>
		   do { e <- equalT
		      ; r <- term 
		      ; return (Strong_equation t r [tokPos e])
		      }
                   <|>
		   do { e <- asKey inS
		      ; s <- sortId 
		      ; return (Membership t s [tokPos e])
		      }
		   <|> return (Mixfix_formula t)
		   }

primFormula = do { c <- asKey trueS
		 ; return (True_atom [tokPos c])
		 }
              <|>
	      do { c <- asKey falseS
		 ; return (False_atom [tokPos c])
		 }
              <|>
	      do { c <- asKey defS
		 ; t <- term
		 ; return (Definedness t [tokPos c])
		 }
              <|>
	      do { c <- try(asKey notS <|> asKey negS) <?> "\"not\""
		 ; f <- primFormula 
		 ; return (Negation f [tokPos c])
		 }
              <|> parenFormula <|> quantFormula <|> termFormula

andKey = asKey lAnd
orKey = asKey lOr

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
implKey = asKey implS
ifKey = asKey ifS

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
		    do { c <- asKey equivS
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
