
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

quMarkT = asKey quMark

qColonT = asKey (colonS++quMark)

forallT = asKey forallS

-----------------------------------------------------------------------------
-- classDecl
-----------------------------------------------------------------------------

pparseDownSet = 
	     do c <- className
		e <- equalT     
	        o <- oBraceT
		i <- typeVar
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
	     fmap ClassName className
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

braces p c = bracketParser p oBraceT cBraceT commaT c


primTypeOrId = fmap TypeToken idToken 
	       <|> braces typeOrId (BracketType Braces)
	       <|> brackets typeOrId (BracketType Squares)
	       <|> bracketParser typeOrId oParenT cParenT commaT
		       (BracketType Parens)
	       
typeOrId = do ts <- many1 primTypeOrId
	      let t = if length ts == 1 then head ts
 		      else MixfixType ts
		 in 
		 kindAnno t
 		 <|> 
		 return(t)

kindAnno ts = do c <- colonT 
		 k <- kind
		 return (KindedType ts k (tokPos c))

primType = typeToken 
	   <|> bracketParser parseType oParenT cParenT commaT 
		   (BracketType Parens)
	   <|> braces parseType (BracketType Braces)
           <|> brackets typeOrId (BracketType Squares)

lazyType = do q <- quMarkT
	      t <- primType 
              return (LazyType t (tokPos q))
	   <|> primType

mixType = do ts <- many1 lazyType
             let t = if length ts == 1 then head ts else MixfixType ts
	       in kindAnno t
		  <|> return t 

prodType = do (ts, ps) <- mixType `separatedBy` crossT
	      return (if length ts == 1 then head ts 
		      else ProductType ts (map tokPos ps)) 

funType = do (ts, as) <- prodType `separatedBy` arrowT
	     return (makeFun ts as)
	       where makeFun [t] [] = t
	             makeFun [t,r] [a] = FunType t (fst a) r (snd a)
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
-- type pattern
-----------------------------------------------------------------------------
typePatternToken :: GenParser Char st TypePattern
typePatternToken = fmap TypePatternToken (pToken (scanWords <|> placeS <|> 
				    reserved (hascasl_type_ops ++
					      formula_ops ++ 
					      hascasl_reserved_ops)
				    scanAnySigns))

primTypePatternOrId = fmap TypePatternToken idToken 
	       <|> braces typePatternOrId (BracketTypePattern Braces)
	       <|> brackets typePatternOrId (BracketTypePattern Squares)
	       <|> bracketParser typePatternArgs oParenT cParenT semiT
		       (BracketTypePattern Parens)

typePatternOrId = do ts <- many1 primTypePatternOrId
		     return( if length ts == 1 then head ts
 			     else MixfixTypePattern ts)

-- to do
typePatternArgs = fmap (\t -> TypePatternArgs 
			(TypeArgs [TypeArg t (ExtClass 
					      (Universe []) InVar [])
				   Other []] []))
		  typeVar  

primTypePattern = typePatternToken 
	   <|> bracketParser typePatternArgs oParenT cParenT semiT 
		   (BracketTypePattern Parens)
	   <|> braces typePattern (BracketTypePattern Braces)
           <|> brackets typePatternOrId (BracketTypePattern Squares)

typePattern = do ts <- many1 primTypePattern
                 let t = if length ts == 1 then head ts 
			 else MixfixTypePattern ts
	           in return t

-----------------------------------------------------------------------------
-- pattern
-----------------------------------------------------------------------------
-- a parsed pattern may also be interpreted as a type (by the mixfix analysis)
-- thus [ ... ] may be a mixfix-pattern, a compound list, 
-- or an instantiation with types

tokenPattern = fmap PatternToken idToken
					  
primPattern = tokenPattern 
	      <|> braces pattern (BracketPattern Braces) 
	      <|> brackets pattern (BracketPattern Squares)
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
-- instOpName
-----------------------------------------------------------------------------
-- places may follow instantiation lists
instOpName = do i@(Id is cs ps) <- uninstOpName
		if isPlace (last is) then return (InstOpName i []) 
		   else do l <- many (brackets parseType Types)
			   u <- many placeT
			   return (InstOpName (Id (is++u) cs ps) l)

-----------------------------------------------------------------------------
-- typeVarDecl, typeScheme
-----------------------------------------------------------------------------

typeVarDecl = do (ts, cs) <- typeVar `separatedBy` commaT
		 do d <- colonT
		    k <- parseClass
		    return (makeTypeVars ts cs d k)
		  <|>
		  do l <- lessT
		     t <- fmap Downset parseType
		     return (makeTypeVars ts cs l t)
	 where makeTypeVars ts cs d k =  
			    zipWith (\t c -> TypeVarDecl t k Comma [tokPos c])
			     (init ts) cs
		              ++ [ TypeVarDecl (last ts) k Other [tokPos d] ]

typeScheme = do f <- forallT
		(ts, cs) <- typeVarDecl `separatedBy` semiT
		d <- dotT
		t <- typeScheme
		return (TypeScheme (concat ts) t (map tokPos (f:cs++[d])))      
	     <|> fmap SimpleTypeScheme parseType

-----------------------------------------------------------------------------
-- term
-----------------------------------------------------------------------------

tToken = pToken(scanFloat <|> scanString 
		       <|> scanQuotedChar <|> scanDotWords <|> scanWords 
		       <|> reserved hascasl_reserved_ops scanAnySigns 
		       <|> placeS <?> "id/literal" )

termToken = fmap TermToken (asKey exEqual <|> tToken)

primTerm = termToken
	   <|> bracketParser term oBraceT cBraceT commaT
		   (BracketTerm Braces)
	   <|> brackets term
		   (BracketTerm Squares)
 	   <|> parenTerm


parenTerm = do o <- oParenT
	       varTerm o
	         <|>
		 qualOpName o
		 <|> 
		 qualPredName o
		 <|>
		 do (ts, ps) <- term `separatedBy` commaT
		    p <- cParenT
		    return (BracketTerm Parens ts (map tokPos (o:ps++[p])))
		     		
partialTypeScheme = do q <- try (qColonT)
		       t <- parseType 
		       return (q, SimpleTypeScheme (LazyType t (tokPos q)))
		    <|> bind (,) colonT typeScheme

varTerm o = do v <- asKey varS
	       i <- var
	       c <- colonT
	       t <- parseType
	       p <- cParenT
	       return (QualVar i t (map tokPos [o,v,c,p]))

qualOpName o = do { v <- asKey opS
		  ; i <- instOpName
 	          ; (c, t) <- partialTypeScheme
		  ; p <- cParenT
		  ; return (QualOp i t (map tokPos [o,v,c,p]))
		  }

predType t = FunType t PFunArr (ProductType [] []) nullPos
predTypeScheme (SimpleTypeScheme t) = SimpleTypeScheme (predType t)
predTypeScheme (TypeScheme vs t ps) = TypeScheme vs (predTypeScheme t) ps

qualPredName o = do { v <- asKey predS
		    ; i <- instOpName
		    ; c <- colonT 
		    ; t <- typeScheme
		    ; p <- cParenT
		    ; return (QualOp i (predTypeScheme t) 
			      (map tokPos [o,v,c,p]))
		  }

term = do ts <- many1 primTerm
	  return (if length ts == 1 then head ts else MixfixTerm ts)


