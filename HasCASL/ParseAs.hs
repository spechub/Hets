
{- HetCATS/HasCASL/ParseAs.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for HasCASL As
-}

module ParseAs where

import Id(tokPos, tokStr)
import Keywords
import Lexer
import HToken
import As
import Parsec

colonT = asKey colonS
lessT = asKey lessS
asT = asKey asP
plusT = asKey plusS
minusT = asKey minusS
dotT = try(asKey dotS <|> asKey cDot) <?> "dot"
crossT = try(asKey prodS <|> asKey timesS) <?> "cross"

-----------------------------------------------------------------------------
-- kind
-----------------------------------------------------------------------------

parseClass = do t <- asKey typeS
		return (Universe [tokPos t])
             <|>
	     fmap ClassName classId
	     <|>
	     do o <- oBraceT
		i <- typeVarId
		d <- dotT
                j <- asKey (tokStr i)
		l <- lessT
                t <- parseType
		c <- cBraceT
		return (Downset i t (map tokPos [o,d,j,l,c])) 
             <|> 
	     do o <- oParenT
		(cs, ps) <- parseClass `separatedBy` commaT
		c <- cParenT
		return (Intersection cs (map tokPos (o:ps++[c])))

extClass = do c <- parseClass
	      do s <- plusT
	         return (ExtClass c CoVar [tokPos s])
	       <|> 
	       do s <- minusT
	          return (ExtClass c ContraVar [tokPos s])
	       <|> return (ExtClass c InVar [])


isClass (ExtClass _ InVar _) = True
isClass _ = False
classOf (ExtClass c _ _) = c

prodClass = do (cs, ps) <- extClass `separatedBy` crossT
	       return (ProdClass cs (map tokPos ps))

kind = kindOrClass [] []

kindOrClass os ps = do c@(ProdClass cs _) <- prodClass
		       if length cs == 1 && isClass (head cs)
		         then curriedKind (os++[c]) ps 
				<|> return (Kind os (classOf (head cs)) 
				     (map tokPos ps))
		         else curriedKind (os++[c]) ps

curriedKind os ps = do a <- asKey funS
		       kindOrClass os (ps++[a])

-----------------------------------------------------------------------------
-- type
-----------------------------------------------------------------------------

parseType = return (MixfixType [])




{-

-----------------------------------------------------------------------------
-- pattern
-----------------------------------------------------------------------------

tokenPattern = fmap PatternToken (pToken (scanQuotedChar <|> scanDotWords 
		 <|> scanDigit <|> scanWords <|> placeS <|> 
		  reserved hascasl_reserved_ops scanAnySigns))
					  
primPattern = bracketPattern oBraceT cBraceT Braces 
	      <|> bracketPattern oBracketT cBracketT Squares
	      <|> bracketPattern oParenT cParenT Parens
	      <|> tokenPattern

bracketPattern op cl k = do { o <- op
			    ; p <- pattern
			    ; c <- cl
			    ; return (BracketPattern k p (map tokPos [o, c]))
			    }

mixPattern = do { l <- many1 primPatter
		; return (if length l == 1 then head l
			  else MixfixPattern l)
		}

commaPattern = do { (ts, ps) <- mixPattern `separatedBy` commaT
		  ; let tp = if length ts == 1 then head ts else 
		           TuplePattern Comma ts (map tokPos ps)
		    in 
		    typedPattern tp
		    <|>  
		    return tp
		  }

typedPattern p = do { c <- colonT
		    ; t <- parseType
		    ; return TypePattern p t [tokPos c]
		    }

semiPattern = do { (ts, ps) <- commaPattern `separatedBy` semiT
		 ; let tp = if length ts == 1 then head ts else    
		           TuplePattern Semicolon ts (map tokPos ps)
		   in
		   asPattern tp
		   <|>
		   return tp
		 }

asPattern p = do { c <- asT 
		 ; t <- pattern 
		 ; return (AsPattern p t [tokPos c])
		 }

pattern = mixPattern 


-}