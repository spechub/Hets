
{- HetCATS/Modal/Formula.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse terms and formulae

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001
   C.2.1 Basic Specifications with Subsorts

   remarks: 
   
   when-else-TERMs are non-mixfix, 
   because when-else has lowest precedence.
   C.3.1 Precedence
 
   Sorted (or casted) terms are not directly recognized, 
   because "u v : s" may be "u (v:s)" or "(u v):s"
   
   No term or formula may start with a parenthesized argument list that
   includes commas.

   The arguments of qualified ops or preds can only be given by a following
   parenthesized argument list.

   Braced or bracketed term-lists including commas stem from a possible 
   %list-annotation or (for brackets) from compound lists.

   C.6.3 Literal syntax for lists
   
   `%list b1__b2, c, f'. 
   b1 must contain at least one open brace or bracket ("{" or [")
   and all brackets must be balanced in "b1 b2" (the empty list).
-}

module CASL.Formula (term, formula, restrictedTerm, restrictedFormula
	       , varDecl, opSort, opFunSort, opType, predType, predUnitType
	       , updFormulaPos) 
    where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import CASL.AS_Basic_CASL
import Common.Lib.Parsec
import CASL.ItemList

simpleTerm :: [String] -> AParser TERM
simpleTerm k = fmap Mixfix_token (pToken(scanFloat <|> scanString 
		       <|>  scanQuotedChar <|> scanDotWords 
		       <|>  reserved (k ++ casl_reserved_fwords) scanAnyWords
		       <|>  reserved (k ++ casl_reserved_fops) scanAnySigns
		       <|>  placeS <?> "id/literal" )) 

startTerm, restTerm, mixTerm, whenTerm  :: [String] -> AParser TERM
startTerm k = parenTerm k <|> braceTerm k <|> bracketTerm k <|> simpleTerm k

restTerm k = startTerm k <|> typedTerm <|> castedTerm

mixTerm k = 
    do l <- startTerm k <:> many (restTerm k)
       return (if length l == 1 then head l else Mixfix_term l)

whenTerm k = 
           do t <- mixTerm k 
	      do w <- asKey whenS
		 f <- impFormula k
		 e <- asKey elseS
		 r <- whenTerm k
		 return (Conditional t f r $ toPos w [] e)
		<|> return t

term :: AParser TERM
term = whenTerm []

restrictedTerm :: [String] -> AParser TERM
restrictedTerm = whenTerm 

typedTerm, castedTerm :: AParser TERM
typedTerm = do c <- colonT
               t <- sortId
               return (Mixfix_sorted_term t [tokPos c])

castedTerm = do c <- asT
		t <- sortId
		return (Mixfix_cast t [tokPos c])

terms :: [String] -> AParser ([TERM], [Token])
terms k = 
    do (ts, ps) <- whenTerm k `separatedBy` anComma
       return (ts, ps)

qualVarName, qualOpName :: Token -> AParser TERM
qualVarName o = do v <- asKey varS
		   i <- varId
		   c <- colonT 
		   s <- sortId
		   p <- cParenT
		   return $ Qual_var i s $ toPos o [v, c] p

qualOpName o = do v <- asKey opS
		  i <- parseId
		  c <- colonST 
		  t <- opType 
		  p <- cParenT
		  return $ Application 
			  (Qual_op_name i t $ toPos o [v, c] p)
			   [] []

opSort :: GenParser Char st (Bool, Id, Pos)
opSort = fmap (\s -> (False, s, nullPos)) sortId 
	 <|> do q <- quMarkT
		s <- sortId
		return (True, s, tokPos q)

opFunSort :: [Id] -> [Token] -> GenParser Char st OP_TYPE
opFunSort ts ps = do a <- pToken (string funS)
		     (b, s, _) <- opSort
		     let qs = map tokPos (ps ++ [a]) in 
			 return (if b then Partial_op_type ts s qs
				 else Total_op_type ts s qs)

opType :: AParser OP_TYPE
opType = do (b, s, p) <- opSort
	    if b then return (Partial_op_type [] s [p])
	       else do c <- crossT 
		       (ts, ps) <- sortId `separatedBy` crossT
		       opFunSort (s:ts) (c:ps)
 	            <|> opFunSort [s] []
	            <|> return (Total_op_type [] s [])

parenTerm, braceTerm, bracketTerm :: [String] -> AParser TERM
parenTerm k = 
            do o <- oParenT
               qualVarName o
		 <|> qualOpName o
		 <|> qualPredName o
		 <|> do (ts, ps) <- terms k
		        c <- cParenT
		        return (Mixfix_parenthesized ts 
				  $ toPos o ps c)

braceTerm k = 
    do o <- oBraceT
       (ts, ps) <- option ([], []) $ terms k
       c <- cBraceT 
       return $ Mixfix_braced ts $ toPos o ps c

bracketTerm k = 
    do o <- oBracketT
       (ts, ps) <- option ([], []) $ terms k
       c <- cBracketT 
       return $ Mixfix_bracketed ts $ toPos o ps c


quant :: AParser (QUANTIFIER, Token)
quant = try(
        do q <- asKey (existsS++exMark)
	   return (Unique_existential, q)
        <|>
        do q <- asKey existsS
	   return (Existential, q)
        <|>
        do q <- forallT
	   return (Universal, q))
        <?> "quantifier"
       
quantFormula :: [String] -> AParser FORMULA
quantFormula k = 
    do (q, p) <- quant
       (vs, ps) <- varDecl `separatedBy` anSemi
       d <- dotT
       f <- impFormula k
       return $ Quantification q vs f
	       $ toPos p ps d

varDecl :: AParser VAR_DECL
varDecl = do (vs, ps) <- varId `separatedBy` anComma
	     c <- colonT
	     s <- sortId
	     return (Var_decl vs s (map tokPos ps ++[tokPos c]))

updFormulaPos :: Pos -> Pos -> FORMULA -> FORMULA
updFormulaPos o c = up_pos_l (\l-> o:l++[c])  

predType :: AParser PRED_TYPE
predType = do (ts, ps) <- sortId `separatedBy` crossT
	      return (Pred_type ts (map tokPos ps))
	   <|> predUnitType

predUnitType :: GenParser Char st PRED_TYPE
predUnitType = do o <- oParenT
		  c <- cParenT
		  return (Pred_type [] [tokPos o, tokPos c])

qualPredName :: Token -> AParser TERM
qualPredName o = do v <- asKey predS
		    i <- parseId
		    c <- colonT 
		    s <- predType
		    p <- cParenT
		    return $ Mixfix_qual_pred
			    $ Qual_pred_name i s $ toPos o [v, c] p

parenFormula :: [String] -> AParser FORMULA
parenFormula k = 
    do o <- oParenT
       do q <- qualPredName o <|> qualVarName o <|> qualOpName o
	  l <- many $ restTerm k  -- optional arguments
	  termFormula k (if null l then q else
				      Mixfix_term (q:l))
         <|> do f <- impFormula k
		case f of Mixfix_formula t -> 
				     do c <- cParenT
					l <- many $ restTerm k
					let tt = Mixfix_parenthesized [t]
					           (toPos o [] c)
					    ft = if null l then tt 
					           else Mixfix_term (tt:l)
					  in termFormula k ft
				     -- commas are not allowed
			  _ -> do c <- cParenT
				  return (updFormulaPos 
						 (tokPos o) (tokPos c) f)

termFormula :: [String] -> TERM -> AParser FORMULA
termFormula k t =  do e <- asKey exEqual
		      r <- whenTerm k
		      return (Existl_equation t r [tokPos e])
                   <|>
		   do try (string exEqual)
		      unexpected ("sign following " ++ exEqual)
                   <|>
		   do e <- equalT
		      r <- whenTerm k
		      return (Strong_equation t r [tokPos e])
                   <|>
		   do e <- asKey inS
		      s <- sortId 
		      return (Membership t s [tokPos e])
		   <|> return (Mixfix_formula t)

primFormula :: [String] -> AParser FORMULA
primFormula k = 
              do c <- asKey trueS
		 return (True_atom [tokPos c])
              <|>
	      do c <- asKey falseS
		 return (False_atom [tokPos c])
              <|>
	      do c <- asKey defS
		 t <- whenTerm k
		 return (Definedness t [tokPos c])
              <|>
	      do c <- try(asKey notS <|> asKey negS) <?> "\"not\""
		 f <- primFormula k 
		 return (Negation f [tokPos c])
              <|> parenFormula k <|> quantFormula k 
		      <|> (whenTerm k >>= termFormula k)


andKey, orKey :: AParser Token
andKey = asKey lAnd
orKey = asKey lOr

andOrFormula :: [String] -> AParser FORMULA
andOrFormula k = 
               do f <- primFormula k
		  do c <- andKey
		     (fs, ps) <- primFormula k `separatedBy` andKey
		     return (Conjunction (f:fs) (map tokPos (c:ps)))
		    <|>
		    do c <- orKey
		       (fs, ps) <- primFormula k `separatedBy` orKey
		       return (Disjunction (f:fs) (map tokPos (c:ps)))
		    <|> return f

implKey, ifKey :: AParser Token
implKey = asKey implS
ifKey = asKey ifS

impFormula :: [String] -> AParser FORMULA
impFormula k = 
             do f <- andOrFormula k
		do c <- implKey
		   (fs, ps) <- andOrFormula k `separatedBy` implKey
		   return (makeImpl (f:fs) (map tokPos (c:ps)))
		  <|>
		  do c <- ifKey
		     (fs, ps) <- andOrFormula k `separatedBy` ifKey
		     return (makeIf (f:fs) (map tokPos (c:ps)))
		  <|>
		  do c <- asKey equivS
		     g <- andOrFormula k
		     return (Equivalence f g [tokPos c])
		  <|> return f
		    where makeImpl [f,g] p = Implication f g p
		          makeImpl (f:r) (c:p) = 
			             Implication f (makeImpl r p) [c]
		          makeImpl _ _ = error "makeImpl got illegal argument"
			  makeIf l p = makeImpl (reverse l) (reverse p)

formula :: AParser FORMULA
formula = impFormula []

restrictedFormula :: [String] -> AParser FORMULA
restrictedFormula = impFormula
