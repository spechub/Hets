
{- HetCATS/HasCASL/ParseTerm.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for HasCASL kind, types, terms and pattern/equations
-}

module ParseTerm where

import Id
import Keywords
import Lexer
import HToken
import As
import Parsec
import AS_Annotation
import Anno_Parser(annotationL)

noQuMark s = try $ asKey s << notFollowedBy (char '?')

colonT = noQuMark colonS
lessT = asKey lessS
equalT = asKey equalS
asT = asKey asP
plusT = asKey plusS
minusT = asKey minusS
dotT = try(asKey dotS <|> asKey cDot) <?> "dot"
crossT = try(asKey prodS <|> asKey timesS) <?> "cross"
barT = asKey barS
quMarkT = asKey quMark

qColonT = asKey (colonS++quMark)

forallT = asKey forallS

-----------------------------------------------------------------------------
-- kind
-----------------------------------------------------------------------------

parseClass = do t <- asKey typeS
		return (Universe (tokPos t))
             <|>
	     fmap ClassName className
             <|> 
	     do o <- oParenT
		(cs, ps) <- parseClass `separatedBy` commaT
		c <- cParenT
		return (Intersection cs (toPos o ps c))

extClass = do c <- parseClass
	      do s <- plusT
	         return (ExtClass c CoVar (tokPos s))
	       <|> 
	       do s <- minusT
	          return (ExtClass c ContraVar (tokPos s))
	       <|> return (ExtClass c InVar nullPos)

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
		  reserved (funS:formula_ops ++ hascasl_reserved_ops) 
		  scanAnySigns)

typeToken :: GenParser Char st Type
typeToken = fmap TypeToken (pToken (scanWords <|> placeS <|> 
				    reserved (hascasl_type_ops ++
					      formula_ops ++
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

kindAnno t = do c <- colonT 
		k <- kind
		return (KindedType t k (tokPos c))

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
	             makeFun [t,r] [a] = FunType t (fst a) r [snd a]
		     makeFun (t:r) (a:b) = makeFun [t, makeFun r b] [a]
		     makeFun _ _ = error "makeFun got illegal argument"

arrowT = do a <- noQuMark funS
	    return (FunArr, tokPos a)
	 <|>
	 do a <- asKey pFun
	    return (PFunArr, tokPos a)
	 <|>
	 do a <- noQuMark contFun
	    return (ContFunArr, tokPos a)
         <|>
	 do a <- asKey pContFun 
	    return (PContFunArr, tokPos a)

parseType :: GenParser Char st Type
parseType = funType  

-----------------------------------------------------------------------------
-- var decls, typevar decls, genVarDecls
-----------------------------------------------------------------------------

varDecls :: GenParser Char st [VarDecl]
varDecls = do (vs, ps) <- var `separatedBy` commaT
	      c <- colonT
	      t <- parseType
	      return (makeVarDecls vs ps t (tokPos c))

makeVarDecls vs ps t q = zipWith (\ v p -> VarDecl v t Comma (tokPos p))
		     (init vs) ps ++ [VarDecl (last vs) t Other q]

typeVarDecls :: GenParser Char st [TypeVarDecl]
typeVarDecls = do (vs, ps) <- typeVar `separatedBy` commaT
		  do   c <- colonT
		       t <- parseClass
		       return (makeTypeVarDecls vs ps t (tokPos c))
		    <|>
		    do l <- lessT
		       t <- parseType
		       return (makeTypeVarDecls vs ps (Downset t) (tokPos l))
		    <|> return (makeTypeVarDecls vs ps 
				(Universe nullPos) nullPos)

makeTypeVarDecls vs ps cl q = zipWith (\ v p -> 
				      TypeVarDecl v cl Comma (tokPos p))
					 (init vs) ps 
			      ++ [TypeVarDecl (last vs) cl Other q]

isSimpleId (Id ts _ _) = null (tail ts) && head (tokStr (head ts)) 
			 `elem` caslLetters

idToToken (Id ts _ _) = head ts

genVarDecls = do (vs, ps) <- var `separatedBy` commaT
		 if all isSimpleId vs then 
		    do   c <- colonT
			 t <- parseType
			 return (map GenVarDecl 
				 (makeVarDecls vs ps t (tokPos c)))
		       <|>
		       do l <- lessT
			  t <- parseType
			  return (map GenTypeVarDecl 
				  (makeTypeVarDecls 
				   (map idToToken vs) ps 
				   (Downset t) (tokPos l)))
		       <|> return(map GenTypeVarDecl 
				  (makeTypeVarDecls 
				   (map idToToken vs) ps 
				   (Universe nullPos) nullPos)) 
		    else
		    do   c <- colonT
			 t <- parseType
			 return (map GenVarDecl 
				 (makeVarDecls vs ps t (tokPos c)))
				 
-----------------------------------------------------------------------------
-- typeArgs
-----------------------------------------------------------------------------

extTypeVar :: GenParser Char st (TypeVar, Variance, Pos) 
extTypeVar = do t <- typeVar
		do   a <- plusT
		     return (t, CoVar, tokPos a)
	 	  <|>
		  do a <- plusT
		     return (t, ContraVar, tokPos a)
		  <|> return (t, InVar, nullPos)

isInVar(_, InVar, _) = True
isInVar(_,_,_) = False		    

typeArgs :: GenParser Char st [TypeArg]
typeArgs = do (ts, ps) <- extTypeVar `separatedBy` commaT
	      do   c <- colonT
                   if all isInVar ts then 
		      do k <- extClass
			 return (makeTypeArgs ts ps (tokPos c) k)
		      else do k <- parseClass
			      return (makeTypeArgs ts ps (tokPos c) 
				      (ExtClass k InVar nullPos))
	        <|> 
	        do l <- lessT
		   t <- parseType
		   return (makeTypeArgs ts ps (tokPos l)
			   (ExtClass (Downset t) InVar nullPos))
		<|> return (makeTypeArgs ts ps nullPos 
			   (ExtClass (Universe nullPos) InVar nullPos))
		where mergeVariance k e (t, InVar, _) p = 
			  TypeArg t e k p 
		      mergeVariance k (ExtClass c _ _) (t, v, ps) p =
			  TypeArg t (ExtClass c v ps) k p
		      makeTypeArgs ts ps q e = 
                         zipWith (mergeVariance Comma e) (init ts) 
				     (map tokPos ps)
			     ++ [mergeVariance Other e (last ts) q]


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

typePatternArgs = fmap TypePatternArgs typeArgs

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
	       ; do { c <- asT 
		    ; t <- mixPattern 
		    ; return (AsPattern v t [tokPos c])
		    } 
		 <|> return v
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
-- typeScheme
-----------------------------------------------------------------------------

typeScheme = do f <- forallT
		(ts, cs) <- typeVarDecls `separatedBy` semiT
		d <- dotT
		t <- typeScheme
		return (TypeScheme (concat ts) t (toPos f cs d))
	     <|> fmap SimpleTypeScheme parseType

-----------------------------------------------------------------------------
-- term
-----------------------------------------------------------------------------

tToken = pToken(scanFloat <|> scanString 
		       <|> scanQuotedChar <|> scanDotWords <|> scanTermWords 
		       <|> reserved hascasl_reserved_ops scanAnySigns 
		       <|> placeS <?> "id/literal" )

termToken = fmap TermToken (asKey exEqual <|> tToken)

-- flag if within brackets: True allows "in"-Terms
primTerm b = termToken
	   <|> braces term (BracketTerm Braces)
	   <|> brackets term  (BracketTerm Squares)
 	   <|> parenTerm
           <|> forallTerm b 
	   <|> exTerm b 
	   <|> lambdaTerm b 
	   <|> caseTerm b
	   <|> letTerm b


parenTerm = do o <- oParenT
	       varTerm o
	         <|>
		 qualOpName o
		 <|> 
		 qualPredName o
		 <|>
		 do (ts, ps) <- option ([],[]) (term `separatedBy` commaT)
		    p <- cParenT
		    return (BracketTerm Parens ts (toPos o ps p))
		     		
partialTypeScheme :: GenParser Char st (Token, TypeScheme)
partialTypeScheme = do q <- qColonT
		       t <- parseType 
		       return (q, SimpleTypeScheme 
			       (FunType (TupleType [] [tokPos q]) 
				PFunArr t [tokPos q]))
		    <|> bind (,) colonT typeScheme

varTerm o = do v <- asKey varS
	       i <- var
	       c <- colonT
	       t <- parseType
	       p <- cParenT
	       return (QualVar i t (toPos o [v, c] p))

qualOpName o = do { v <- asKey opS
		  ; i <- instOpName
 	          ; (c, t) <- partialTypeScheme
		  ; p <- cParenT
		  ; return (QualOp i t (toPos o [v, c] p))
		  }

predType t = FunType t PFunArr (ProductType [] []) []
predTypeScheme (SimpleTypeScheme t) = SimpleTypeScheme (predType t)
predTypeScheme (TypeScheme vs t ps) = TypeScheme vs (predTypeScheme t) ps

qualPredName o = do { v <- asKey predS
		    ; i <- instOpName
		    ; c <- colonT 
		    ; t <- typeScheme
		    ; p <- cParenT
		    ; return (QualOp i (predTypeScheme t) 
			      (toPos o [v, c] p))
		  }

typeQual b = 
	      do q <- colonT
	         return (OfType, q)
	      <|> 
	   if b then 
	      do q <- asKey asS
	         return (AsType, q)
	      <|> 
	      do q <- asKey inS
		 return (InType, q)
	   else
	      do q <- asKey asS
	         return (AsType, q)

typedTerm f b = 
    do (q, p) <- typeQual b
       t <- parseType
       return (TypedTerm f q t (tokPos p))

mixTerm b = 
    do ts <- many1 $ primTerm b
       let t = if length ts == 1 then head ts else MixfixTerm ts
	   in typedTerm t b <|> return t

wTerm b = 
    do t <- mixTerm b 
       whereTerm b t <|> return t

term = wTerm True
-----------------------------------------------------------------------------
-- quantified term
-----------------------------------------------------------------------------

forallTerm b = 
             do f <- forallT
		(vs, ps) <- genVarDecls `separatedBy` semiT
		d <- dotT
		t <- wTerm b
		return (QuantifiedTerm Universal (concat vs) t 
			(toPos f ps d))

exQuant =
        do { q <- asKey (existsS++exMark)
	   ; return (Unique, q)
	   }
        <|>
        do { q <- asKey existsS
	   ; return (Existential, q)
	   }

exTerm b = 
         do { (q, p) <- exQuant
	    ; (vs, ps) <- varDecls `separatedBy` semiT
	    ; d <- dotT
	    ; f <- wTerm b
	    ; return (QuantifiedTerm q (map GenVarDecl (concat vs)) f
		      (toPos p ps d))
	    }

lamDot = do d <- asKey (dotS++exMark) <|> asKey (cDot++exMark)
	    return (Total,d)
	 <|> 
	 do d <- dotT
	    return (Partial,d)

lambdaTerm b = 
             do l <- asKey lamS
		pl <- lamPattern
		(k, d) <- lamDot      
		t <- wTerm b
		return (LambdaTerm pl k t (toPos l [] d))

lamPattern = do (vs, ps) <- varDecls `separatedBy` semiT
		return [PatternVars (concat vs) (map tokPos ps)]
	     <|> 
	     many (bracketParser patterns oParenT cParenT semiT 
		      (BracketPattern Parens)) 

-----------------------------------------------------------------------------
-- case-term
-----------------------------------------------------------------------------
-- True allows "in"-Terms

patternTermPair :: Bool -> String -> GenParser Char st ProgEq
patternTermPair b sep = do p <- pattern
			   s <- asKey sep
			   t <- wTerm b
			   return (ProgEq p t (tokPos s))

caseTerm b = 
           do c <- asKey caseS
	      t <- term
	      o <- asKey ofS
	      (ts, ps) <- patternTermPair b funS `separatedBy` barT
	      return (CaseTerm t ts (map tokPos (c:o:ps)))

-----------------------------------------------------------------------------
-- annos and lookahead after ";"
-----------------------------------------------------------------------------
-- skip to leading annotation and read many
annos :: GenParser Char st [Annotation]
annos = skip >> many (annotationL << skip)

tryItemEnd :: [String] -> GenParser Char st ()
tryItemEnd l = 
    try (do { c <- lookAhead (annos >> 
                              (single (oneOf "\"([{")
                               <|> placeS
                               <|> scanAnySigns
                               <|> many scanLPD))
            ; if null c || c `elem` l then return () else unexpected c
            })


-- "axiom/axioms ... ; exists ... " is not supported 
startKeyword = dotS:cDot: hascasl_reserved_words

-----------------------------------------------------------------------------
-- where-term
-----------------------------------------------------------------------------

whereEquations b = 
             do { p <- patternTermPair b equalS
		; do { s <- semiT
                     ; do { tryItemEnd startKeyword
                          ; return ([p], [s])
                          }
                       <|> 
                       do { (ps, ts) <- whereEquations b 
                          ; return (p:ps, s:ts)
                          }
                     }
                  <|>
                  return ([p], [])
		}

whereTerm b t = 
              do w <- asKey whereS
		 (ts, ps) <- whereEquations b
		 return (LetTerm ts t (map tokPos (w:ps)))

letTerm b = 
          do l <- asKey letS
	     (es, ps) <- patternTermPair False equalS `separatedBy` semiT 
	     i <- asKey inS
	     t <- wTerm b
	     return (LetTerm es t (toPos l ps i))