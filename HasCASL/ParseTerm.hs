
{- HetCATS/HasCASL/ParseTerm.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for HasCASL kind, types, terms and pattern/equations
-}

module HasCASL.ParseTerm where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import HasCASL.HToken
import HasCASL.As
import Common.Lib.Parsec

noQuMark :: String -> AParser Token
noQuMark s = try $ asKey s << notFollowedBy (char '?')

colT, plusT, minusT, qColonT :: AParser Token

colT = noQuMark colonS
plusT = asKey plusS
minusT = asKey minusS
qColonT = asKey (colonS++quMark)

quColon :: AParser (Partiality, Token)
quColon = do c <- colT
	     return (Total, c)
	  <|> 
	  do c <- qColonT
	     return (Partial, c) 

-----------------------------------------------------------------------------
-- kind
-----------------------------------------------------------------------------
-- universe is just a special classId ("Type")
parseClassId :: AParser Kind
parseClassId = fmap (\c -> if showId c "" == "Type" 
		   then Universe [posOfId c]
		   else ClassKind c MissingKind) classId

parseSimpleKind :: AParser Kind
parseSimpleKind = parseClassId
             <|> 
	     do o <- oParenT
		(cs, ps) <- kind `separatedBy` anComma
		c <- cParenT
		return (if isSingle cs then head cs else
			Intersection cs	(toPos o ps c))
             <|>
	     do o <- oBraceT
	        i <- pToken scanWords
		d <- dotT
		j <- asKey (tokStr i)
		l <- lessT
		t <- parseType
		p <- cBraceT
		return (Downset (Just i) t MissingKind 
			(map tokPos [o,d,j,l,p])) 

parseExtKind :: AParser ExtKind
parseExtKind = do k <- parseSimpleKind
	          do s <- plusT
		     return (ExtKind k CoVar [tokPos s])
                   <|>
		   do m <- minusT
		      return (ExtKind k ContraVar [tokPos m])
                   <|> return (ExtKind k InVar [])

kind :: AParser Kind
kind = 
    do k1 <- parseExtKind
       do a <- asKey funS
	  k2 <- kind
	  return (FunKind k1 k2 $ [tokPos a])
        <|> case k1 of
	    ExtKind k InVar _  -> return k
	    _  -> unexpected "variance of kind"

extKind :: AParser ExtKind
extKind = 
    do k1 <- parseExtKind
       do a <- asKey funS
	  k2 <- kind
	  return (ExtKind (FunKind k1 k2 $ [tokPos a]) InVar [])
        <|> return k1

-----------------------------------------------------------------------------
-- type
-----------------------------------------------------------------------------
-- a parsed type may also be interpreted as a kind (by the mixfix analysis)

typeToken :: AParser Type
typeToken = fmap TypeToken (pToken (scanWords <|> placeS <|> 
				    reserved (lessS : equalS : barS :
					      hascasl_type_ops 
					      ++ hascasl_reserved_ops)
				    scanSigns))

mkBraces :: AParser a -> ([a] -> [Pos] -> b) 
       -> AParser b
mkBraces p c = bracketParser p oBraceT cBraceT anComma c

type TokenMode = [String]   

-- [...] may contain types or ids
aToken :: TokenMode -> AParser Token
aToken b = pToken (scanQuotedChar <|> scanDotWords 
		   <|> scanDigit <|> scanWords <|> placeS <|> 
		   reserved b scanSigns)

idToken :: AParser Token
idToken = aToken []

primTypeOrId, typeOrId :: AParser Type
primTypeOrId = fmap TypeToken idToken
	       <|> mkBraces typeOrId (BracketType Braces)
	       <|> mkBrackets typeOrId (BracketType Squares)
	       <|> bracketParser typeOrId oParenT cParenT anComma
		       (BracketType Parens)
	       
typeOrId = do ts <- many1 primTypeOrId
	      let t = if isSingle ts then head ts
 		      else MixfixType ts
		 in 
		 kindAnno t
 		 <|> 
		 return(t)

kindAnno :: Type -> AParser Type
kindAnno t = do c <- colT 
		k <- kind
		return (KindedType t k [tokPos c])

primType, lazyType, mixType, prodType, funType :: AParser Type
primType = typeToken 
	   <|> bracketParser parseType oParenT cParenT anComma 
		   (BracketType Parens)
	   <|> mkBraces parseType (BracketType Braces)
           <|> mkBrackets typeOrId (BracketType Squares)

lazyType = do q <- quMarkT
	      t <- primType 
              return (LazyType t [tokPos q])
	   <|> primType

mixType = do ts <- many1 lazyType
             let t = if isSingle ts then head ts else MixfixType ts
	       in kindAnno t
		  <|> return t 

prodType = do (ts, ps) <- mixType `separatedBy` crossT
	      return (if isSingle ts then head ts 
		      else ProductType ts (map tokPos ps)) 

funType = do t1 <- prodType 
	     do a <- arrowT
		t2 <- funType
		return $ FunType t1 (fst a) t2 [snd a] 
	       <|> return t1

arrowT :: AParser (Arrow, Pos)
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

parseType :: AParser Type
parseType = funType  

-----------------------------------------------------------------------------
-- var decls, typevar decls, genVarDecls
-----------------------------------------------------------------------------

varDecls :: AParser [VarDecl]
varDecls = do (vs, ps) <- var `separatedBy` anComma
	      varDeclType vs ps

varDeclType :: [Var] -> [Token] -> AParser [VarDecl]
varDeclType vs ps = do c <- colT
		       t <- parseType
		       return (makeVarDecls vs ps t (tokPos c))

makeVarDecls :: [Var] -> [Token] -> Type -> Pos -> [VarDecl]
makeVarDecls vs ps t q = zipWith (\ v p -> VarDecl v t Comma [tokPos p])
		     (init vs) ps ++ [VarDecl (last vs) t Other [q]]

varDeclDownSet :: [TypeId] -> [Token] -> AParser [TypeArg]
varDeclDownSet vs ps = 
		    do l <- lessT
		       t <- parseType
		       return (makeTypeVarDecls vs ps 
			       (ExtKind (Downset Nothing t MissingKind []) 
				InVar [])(tokPos l))

typeVarDecls :: AParser [TypeArg]
typeVarDecls = do (vs, ps) <- typeVar `separatedBy` anComma
		  do   c <- colT
		       t <- extKind
		       return (makeTypeVarDecls vs ps t (tokPos c))
		    <|> varDeclDownSet vs ps
		    <|> return (makeTypeVarDecls vs ps 
				(ExtKind star InVar []) nullPos)

makeTypeVarDecls :: [TypeId] -> [Token] -> ExtKind -> Pos -> [TypeArg]
makeTypeVarDecls vs ps cl q = 
    zipWith (\ v p -> 
	     TypeArg v cl Comma [tokPos p])
		(init vs) ps 
		++ [TypeArg (last vs) cl Other [q]]

genVarDecls:: AParser [GenVarDecl]
genVarDecls = do (vs, ps) <- typeVar `separatedBy` anComma
		 fmap (map GenVarDecl) (varDeclType vs ps)
		      <|> fmap (map GenTypeVarDecl)
			       (varDeclDownSet vs ps)
				 
-----------------------------------------------------------------------------
-- typeArgs
-----------------------------------------------------------------------------

extTypeVar :: AParser (TypeId, Variance, Pos) 
extTypeVar = do t <- restrictedVar [lessS, plusS, minusS]
		do   a <- plusT
		     return (t, CoVar, tokPos a)
	 	  <|>
		  do a <- minusT
		     return (t, ContraVar, tokPos a)
		  <|> return (t, InVar, nullPos)

-- relaxed restriction for funKind (products should be disallowed)
typeArgs :: AParser [TypeArg]
typeArgs = do (ts, ps) <- extTypeVar `separatedBy` anComma
	      do   c <- colT
                   if let isInVar(_, InVar, _) = True
			  isInVar(_,_,_) = False
		      in all isInVar ts then 
		      do k <- extKind
			 return (makeTypeArgs ts ps [tokPos c] k)
		      else do k <- kind
			      return (makeTypeArgs ts ps [tokPos c] 
				      (ExtKind k InVar []))
	        <|> 
	        do l <- lessT
		   t <- parseType
		   return (makeTypeArgs ts ps [tokPos l]
			   (ExtKind (Downset Nothing t MissingKind []) 
			    InVar []))
		<|> return (makeTypeArgs ts ps [] (ExtKind star InVar []))
		where mergeVariance k (ExtKind e InVar _) (t, v, ps) p =
			  TypeArg t (ExtKind e v [ps]) k p
		      mergeVariance k e (t, _, _) p = 
			  TypeArg t e k p 
		      makeTypeArgs ts ps q e = 
                         zipWith (mergeVariance Comma e) (init ts) 
				     (map ((:[]). tokPos) ps)
			     ++ [mergeVariance Other e (last ts) q]

-----------------------------------------------------------------------------
-- type pattern
-----------------------------------------------------------------------------


singleTypeArg :: AParser TypeArg
singleTypeArg = do  as <- typeArgs 
		    case as of 
			    [a] -> return a 
			    _ -> unexpected "list of type arguments"

typePatternToken, primTypePatternOrId, typePatternOrId, typePatternArg
    :: AParser TypePattern

typePatternArg = 
    do o <- oParenT
       a <- singleTypeArg
       p <- cParenT
       return $ TypePatternArg a $ toPos o [] p

typePatternToken = fmap TypePatternToken (pToken (scanWords <|> placeS <|> 
				    reserved [lessS, equalS] scanSigns))

primTypePatternOrId = fmap TypePatternToken idToken 
	       <|> mkBraces typePatternOrId (BracketTypePattern Braces)
	       <|> mkBrackets typePatternOrId (BracketTypePattern Squares)
	       <|> typePatternArg

typePatternOrId = do ts <- many1 primTypePatternOrId
		     return( if isSingle ts then head ts
 			     else MixfixTypePattern ts)

primTypePattern, typePattern :: AParser TypePattern

primTypePattern = typePatternToken 
	   <|> typePatternArg
	   <|> mkBraces typePattern (BracketTypePattern Braces)
           <|> mkBrackets typePatternOrId (BracketTypePattern Squares)

typePattern = do ts <- many1 primTypePattern
                 let t = if isSingle ts then head ts 
			 else MixfixTypePattern ts
	           in return t

-----------------------------------------------------------------------------
-- pattern
-----------------------------------------------------------------------------
-- a parsed pattern may also be interpreted as a type (by the mixfix analysis)
-- thus [ ... ] may be a mixfix-pattern, a compound list, 
-- or an instantiation with types

-- special pattern needed that don't contain "->" at the top-level
-- because "->" should be recognized in case-expressions

-- flag b allows "->" in patterns 

tokenPattern :: TokenMode -> AParser Pattern
tokenPattern b = fmap PatternToken (aToken b)
					  
primPattern :: TokenMode -> AParser Pattern
primPattern b = tokenPattern b 
		<|> mkBraces pattern (BracketPattern Braces) 
		<|> mkBrackets pattern (BracketPattern Squares)
		<|> bracketParser pattern oParenT cParenT anComma
			(BracketPattern Parens)

mixPattern :: TokenMode -> AParser Pattern
mixPattern b = 
    do l <- many1 $ primPattern b
       let p = if isSingle l then head l else MixfixPattern l
	   in typedPattern p <|> return p

typedPattern :: Pattern -> AParser Pattern
typedPattern p = do { c <- colT
		    ; t <- parseType
		    ; return (TypedPattern p t [tokPos c])
		    }

asPattern :: TokenMode -> AParser Pattern
asPattern b = 
    do v <- mixPattern b
       do   c <- asKey asP 
	    t <- mixPattern b 
	    return (AsPattern v t [tokPos c])
         <|> return v

pattern :: AParser Pattern
pattern = asPattern []

-----------------------------------------------------------------------------
-- instOpId
-----------------------------------------------------------------------------
-- places may follow instantiation lists

instOpId :: AParser InstOpId
instOpId = do i@(Id is cs ps) <- uninstOpId
	      if isPlace (last is) then return (InstOpId i [] []) 
		   else do (ts, qs) <- option ([], [])
				       (mkBrackets parseType (,))
			   u <- many placeT
			   return (InstOpId (Id (is++u) cs ps) ts qs)

-----------------------------------------------------------------------------
-- typeScheme
-----------------------------------------------------------------------------

typeScheme :: AParser TypeScheme
typeScheme = do f <- forallT
		(ts, cs) <- typeVarDecls `separatedBy` anSemi
		d <- dotT
		t <- typeScheme
                return $ case t of 
			 TypeScheme ots q ps ->
			     TypeScheme (concat ts ++ ots) q 
					(toPos f cs d ++ ps)
	     <|> fmap simpleTypeScheme parseType

-----------------------------------------------------------------------------
-- term
-----------------------------------------------------------------------------

tToken :: AParser Token
tToken = pToken(scanFloat <|> scanString 
		<|> scanQuotedChar <|> scanDotWords 
		<|> reserved [ifS] scanWords 
		<|> reserved [barS] scanSigns 
		<|> placeS <?> "id/literal" )

termToken :: AParser Term
termToken = fmap TermToken (asKey exEqual <|> asKey equalS <|> tToken)

primTerm :: AParser Term
primTerm = termToken
	   <|> mkBraces term (BracketTerm Braces)
	   <|> mkBrackets term (BracketTerm Squares)
 	   <|> parenTerm

-- flag WithIn allows "in"-Terms
baseTerm :: TypeMode -> AParser Term
baseTerm b = ifTerm b
           <|> forallTerm b 
	   <|> exTerm b 
	   <|> lambdaTerm b 
	   <|> caseTerm b
	   <|> letTerm b

ifTerm :: TypeMode -> AParser Term
ifTerm b = 
    do i <- asKey ifS
       c <- mixTerm b
       do t <- asKey thenS
	  e <- mixTerm b
	  return (MixfixTerm [TermToken i, c, TermToken t, e])
	<|> return (MixfixTerm [TermToken i, c])

parenTerm :: AParser Term
parenTerm = do o <- oParenT
	       varTerm o
	         <|>
		 qualOpName o
		 <|> 
		 qualPredName o
		 <|>
		 do (ts, ps) <- option ([],[]) (term `separatedBy` anComma)
		    p <- cParenT
		    return (BracketTerm Parens ts (toPos o ps p))
		     		
partialTypeScheme :: AParser (Token, TypeScheme)
partialTypeScheme = do q <- qColonT
		       t <- parseType 
		       return (q, simpleTypeScheme 
			       (FunType (BracketType Parens [] [tokPos q]) 
				PFunArr t [tokPos q]))
		    <|> bind (,) colT typeScheme

varTerm :: Token -> AParser Term
varTerm o = do v <- asKey varS
	       i <- var
	       c <- colT
	       t <- parseType
	       p <- cParenT
	       return (QualVar i t (toPos o [v, c] p))

qualOpName :: Token -> AParser Term
qualOpName o = do { v <- asKey opS <|> asKey functS
		  ; i <- instOpId
 	          ; (c, t) <- partialTypeScheme
		  ; p <- cParenT
		  ; return (QualOp i t (toPos o [v, c] p))
		  }

qualPredName :: Token -> AParser Term
qualPredName o = do { v <- asKey predS
		    ; i <- instOpId
		    ; c <- colT 
		    ; t <- typeScheme
		    ; p <- cParenT
		    ; return (QualOp i (predTypeScheme t) 
			      (toPos o [v, c] p))
		  }

data TypeMode = NoIn | WithIn

typeQual :: TypeMode -> AParser (TypeQual, Token) 
typeQual m = 
	      do q <- colT
	         return (OfType, q)
	      <|> 
	      do q <- asT
	         return (AsType, q)
	      <|> 
	      case m of 
		     NoIn -> pzero
		     WithIn -> 
			 do q <- asKey inS
			    return (InType, q)

typedTerm :: TypeMode -> AParser Term
typedTerm b = 
    do t <- primTerm
       do (q, p) <- typeQual b
	  ty <- parseType
	  return (TypedTerm t q ty [tokPos p])
        <|> return t
      <|> baseTerm b

mixTerm :: TypeMode -> AParser Term
mixTerm b = 
    do ts <- many1 $ typedTerm b
       return $ if isSingle ts then head ts else MixfixTerm ts

term :: AParser Term
term = mixTerm WithIn
       
-----------------------------------------------------------------------------
-- quantified term
-----------------------------------------------------------------------------

forallTerm :: TypeMode -> AParser Term
forallTerm b = 
             do f <- forallT
		(vs, ps) <- genVarDecls `separatedBy` anSemi
		addAnnos
		d <- dotT
		t <- mixTerm b
		return (QuantifiedTerm Universal (concat vs) t 
			(toPos f ps d))

exQuant :: AParser (Quantifier, Token)
exQuant =
        do { q <- asKey (existsS++exMark)
	   ; return (Unique, q)
	   }
        <|>
        do { q <- asKey existsS
	   ; return (Existential, q)
	   }

exTerm :: TypeMode -> AParser Term
exTerm b = 
         do { (q, p) <- exQuant
	    ; (vs, ps) <- varDecls `separatedBy` anSemi
	    ; d <- dotT
	    ; f <- mixTerm b
	    ; return (QuantifiedTerm q (map GenVarDecl (concat vs)) f
		      (toPos p ps d))
	    }

lamDot :: AParser (Partiality, Token)
lamDot = do d <- asKey (dotS++exMark) <|> asKey (cDot++exMark)
	    return (Total,d)
	 <|> 
	 do d <- dotT
	    return (Partial,d)

lambdaTerm :: TypeMode -> AParser Term
lambdaTerm b = 
             do l <- asKey lamS
		pl <- lamPattern
		(k, d) <- lamDot      
		t <- mixTerm b
		return (LambdaTerm pl k t (toPos l [] d))

lamPattern :: AParser [Pattern]
lamPattern = 
    do  lookAhead lamDot 
	return []
      <|> do p <- pattern
	     ps <- lamPattern
	     return (p : ps)

-----------------------------------------------------------------------------
-- case-term
-----------------------------------------------------------------------------
-- b1 allows "->", b2 allows "in"-Terms

patternTermPair :: TokenMode -> TypeMode -> String -> AParser ProgEq
patternTermPair b1 b2  sep = 
    do p <- asPattern b1
       s <- asKey sep
       t <- mixTerm b2
       return (ProgEq p t (tokPos s))

caseTerm :: TypeMode -> AParser Term
caseTerm b = 
           do c <- asKey caseS
	      t <- term
	      o <- asKey ofS
	      (ts, ps) <- patternTermPair ([funS]) b funS 
			  `separatedBy` barT
	      return (CaseTerm t ts (map tokPos (c:o:ps)))

-----------------------------------------------------------------------------
-- let-term
-----------------------------------------------------------------------------

letTerm :: TypeMode -> AParser Term
letTerm b = 
          do l <- asKey letS
	     (es, ps) <- patternTermPair ([equalS]) NoIn equalS 
			 `separatedBy` anSemi 
	     i <- asKey inS
	     t <- mixTerm b
	     return (LetTerm es t (toPos l ps i))
