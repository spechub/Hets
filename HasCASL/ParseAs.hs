
{- HetCATS/HasCASL/ParseAs.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for HasCASL As
-}

module ParseAs where

import Id
import Keywords
import Lexer
import HToken
import As
import Parsec

colonT = asKey colonS
lessT = asKey lessS
equalT = asKey equalS
asT = asKey asP
plusT = asKey plusS
minusT = asKey minusS
dotT = try(asKey dotS <|> asKey cDot) <?> "dot"
crossT = try(asKey prodS <|> asKey timesS) <?> "cross"


-----------------------------------------------------------------------------
-- classDecl
-----------------------------------------------------------------------------

pparseDownSet = 
	     do c <- classId
		e <- equalT     
	        o <- oBraceT
		i <- typeVarId
		d <- dotT
                j <- asKey (tokStr i)
		l <- lessT
                t <- parseType
		p <- cBraceT
		return (DownsetDefn c i t (map tokPos [e,o,d,j,l,p])) 

-----------------------------------------------------------------------------
-- kind
-----------------------------------------------------------------------------

parseClass = do t <- asKey typeS
		return (Universe [tokPos t])
             <|>
	     fmap ClassName classId
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
-- a parsed type may also be interpreted as a kind (by the mixfix analysis)

idToken = pToken (scanQuotedChar <|> scanDotWords 
		 <|> scanDigit <|> scanWords <|> placeS <|> 
		  reserved hascasl_reserved_ops scanAnySigns)

typeToken :: GenParser Char st Type
typeToken = fmap TypeToken (pToken (toKey typeS <|> scanWords <|> placeS <|> 
				    reserved (hascasl_type_ops ++
					      hascasl_reserved_ops)
				    scanAnySigns))

typeOrId = do ts <- many1(fmap TypeOrIdToken idToken 
			  <|> brackets typeOrId oBraceT cBraceT 
			  (BracketTypeOrId Braces)
			  <|> brackets typeOrId oBracketT cBracketT 
			  (BracketTypeOrId Squares)
			  <|> brackets typeOrId oParenT cParenT 
			  (BracketTypeOrId Parens)
			  <|> kindAnno KindAnnotation)
	      return( if length ts == 1 then head ts
 		      else MixfixTypeOrId ts)

kindAnno :: (Kind -> [Pos] -> b) -> GenParser Char st b 
kindAnno constr = do c <- colonT 
		     k <- kind
		     return (constr k [tokPos c])

bracketParser :: GenParser Char st a -> GenParser Char st Token 
	 -> GenParser Char st Token -> GenParser Char st Token
	 -> ([a] -> [Pos] -> b) -> GenParser Char st b
bracketParser parser op cl sep k = 
    do o <- op
       (ts, ps) <- option ([], []) 
		   (parser `separatedBy` sep)
       c <- cl
       return (k ts (map tokPos (o:ps++[c])))

brackets parser op cl k = bracketParser parser op cl commaT k

primType = typeToken 
	   <|> brackets parseType oParenT cParenT (BracketType Parens)
	   <|> brackets parseType oBraceT cBraceT (BracketType Braces)
           <|> brackets typeOrId oBracketT cBracketT MixCompound

mixType = do ts <- many1 primType
             let t = if length ts == 1 then head ts else MixfixType ts
	       in kindAnno (KindedType t)
		  <|> return t 

prodType = do (ts, ps) <- mixType `separatedBy` crossT
	      return (if length ts == 1 then head ts 
		      else ProductType ts (map tokPos ps)) 

funType = do (ts, as) <- prodType `separatedBy` arrowT
	     return (makeFun ts as)
	       where makeFun [t] [] = t
	             makeFun [t,r] [a] = FunType t (fst a) r [snd a] 
		     makeFun (t:r) (a:b) = makeFun [t, makeFun r b] [a] 

arrowT = do a <- try(asKey funS) 
	    return (FunArr, tokPos a)
	 <|>
	 do a <- try(asKey pFun) 
	    return (PFunArr, tokPos a)
	 <|>
	 do a <- try(asKey contFun) 
	    return (ContFunArr, tokPos a)
         <|>
	 do a <- try(asKey pContFun) 
	    return (PContFunArr, tokPos a)

parseType :: GenParser Char st Type
parseType = funType  

-----------------------------------------------------------------------------
-- pattern
-----------------------------------------------------------------------------
-- a parsed pattern may also be interpreted as a type (by the mixfix analysis)
-- thus [ ... ] may be a mixfix-pattern, a compound list, 
-- or an instantiation with types

tokenPattern = fmap PatternToken idToken
					  
primPattern = tokenPattern 
	      <|> bracketParser pattern oBraceT cBraceT commaT 
		  (BracketPattern Braces) 
	      <|> bracketParser pattern oBracketT cBracketT commaT 
		  (BracketPattern Squares)
	      <|> bracketParser patterns oParenT cParenT semiT 
		  (BracketPattern Parens)

patterns = do { (ts, ps) <- pattern `separatedBy` commaT
	      ; let tp = if length ts == 1 then head ts else 
		            TuplePattern ts (map tokPos ps)
		in return tp
	      }

mixPattern = do l <- many1 primPattern
                let p = if length l == 1 then head l else MixfixPattern l
		  in typedPattern p
		     <|> return p

typedPattern p = do { c <- colonT
		    ; t <- parseType
		    ; return (TypedPattern p t [tokPos c])
		    }

asPattern = do { v <- mixPattern
	       ; c <- asT 
	       ; t <- mixPattern 
	       ; return (AsPattern v t [tokPos c])
	       }

pattern = asPattern

-----------------------------------------------------------------------------
-- term
-----------------------------------------------------------------------------

termToken = fmap TermToken idToken

primTerm = termToken
	   <|> brackets term oBraceT cBraceT
		   (BracketTerm Braces)
	   <|> brackets term oBracketT cBracketT 
		   (BracketTerm Squares)
-- 	   <|> parenTerm

term = do ts <- many1 primTerm
	  return (if length ts == 1 then head ts else MixfixTerm ts)