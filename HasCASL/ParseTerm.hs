
{- HetCATS/HasCASL/ParseTerm.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for HasCASL kind, types, terms and pattern/equations
-}

module ParseTerm where

import AnnoState
import Id
import Keywords
import Lexer
import List(nub)
import Token
import HToken
import As
import Parsec
import ItemList

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
parseClassId :: AParser Class
parseClassId = fmap (\c -> if showId c "" == "Type" 
		   then Intersection [] [posOfId c]
		   else Intersection [c] []) classId

parseClass :: AParser Class
parseClass = parseClassId
             <|> 
	     do o <- oParenT
		(cs, ps) <- parseClass `separatedBy` anComma
		c <- cParenT
		return (Intersection (nub $ concatMap iclass cs) 
			(toPos o ps c))

parsePlainClass :: AParser Kind
parsePlainClass = 
             fmap PlainClass parseClassId 
             <|> 
	     do o <- oParenT
		f <- funKind
		case f of 
		  PlainClass k -> do
		      p <- anComma
		      (cs, ps) <- parseClass `separatedBy` anComma
		      c <- cParenT
		      return $ PlainClass $ Intersection 
				 (nub $ concatMap iclass (k:cs)) 
					    (toPos o (p:ps) c)
		    <|> do cParenT >> return f
		  _ ->  cParenT >> return f

extClass :: AParser Kind
extClass = do c <- parsePlainClass
	      case c of ExtClass _ _ _ -> return c
			_ -> do 
			     s <- plusT
			     return (ExtClass c CoVar [tokPos s])
			 <|> do 
			     s <- minusT
			     return (ExtClass c ContraVar [tokPos s])
			 <|> return c

prodClass :: AParser Kind
prodClass = do (cs, ps) <- extClass `separatedBy` crossT
	       return $ if length cs == 1 then head cs 
		      else ProdClass cs (map tokPos ps)

checkResultKind :: Kind -> AParser Kind
checkResultKind k = case k of 
		     ExtClass _ _ _ -> unexpected "variance of result kind"
		     ProdClass _ _ -> unexpected "product result kind"
		     _ -> return k

funKind, kind :: AParser Kind
funKind = 
    do k1 <- prodClass
       do a <- asKey funS
	  k2 <- kind
	  return $ KindAppl k1 k2 $ [tokPos a]
        <|> return k1

kind = funKind >>= checkResultKind

-----------------------------------------------------------------------------
-- type
-----------------------------------------------------------------------------
-- a parsed type may also be interpreted as a kind (by the mixfix analysis)

typeToken :: AParser Type
typeToken = fmap TypeToken (pToken (scanWords <|> placeS <|> 
				    reserved (equalS: hascasl_type_ops)
				    scanSigns))

mkBraces :: AParser a -> ([a] -> [Pos] -> b) 
       -> AParser b
mkBraces p c = bracketParser p oBraceT cBraceT anComma c

data TokenMode = AnyToken
               | NoToken String   

-- [...] may contain types or ids
aToken :: TokenMode -> AParser Token
aToken b = pToken (scanQuotedChar <|> scanDotWords 
		   <|> scanDigit <|> scanWords <|> placeS <|> 
		   case b of 
		   AnyToken -> scanSigns 
		   NoToken s -> reserved [s] scanSigns)

idToken :: AParser Token
idToken = aToken AnyToken

primTypeOrId, typeOrId :: AParser Type
primTypeOrId = fmap TypeToken idToken
	       <|> mkBraces typeOrId (BracketType Braces)
	       <|> mkBrackets typeOrId (BracketType Squares)
	       <|> bracketParser typeOrId oParenT cParenT anComma
		       (BracketType Parens)
	       
typeOrId = do ts <- many1 primTypeOrId
	      let t = if length ts == 1 then head ts
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
             let t = if length ts == 1 then head ts else MixfixType ts
	       in kindAnno t
		  <|> return t 

prodType = do (ts, ps) <- mixType `separatedBy` crossT
	      return (if length ts == 1 then head ts 
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
			       (PlainClass (Downset t)) (tokPos l))

typeVarDecls :: AParser [TypeArg]
typeVarDecls = do (vs, ps) <- typeVar `separatedBy` anComma
		  do   c <- colT
		       t <- kind
		       return (makeTypeVarDecls vs ps t (tokPos c))
		    <|> varDeclDownSet vs ps
		    <|> return (makeTypeVarDecls vs ps 
				nullKind nullPos)

makeTypeVarDecls :: [TypeId] -> [Token] -> Kind -> Pos -> [TypeArg]
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

typeArgs :: AParser [TypeArg]
typeArgs = do (ts, ps) <- extTypeVar `separatedBy` anComma
	      do   c <- colT
                   if let isInVar(_, InVar, _) = True
			  isInVar(_,_,_) = False
		      in all isInVar ts then 
		      do k <- kind
			 return (makeTypeArgs ts ps [tokPos c] k)
		      else do k <- kind
			      return (makeTypeArgs ts ps [tokPos c] 
				      (ExtClass k InVar []))
	        <|> 
	        do l <- lessT
		   t <- parseType
		   return (makeTypeArgs ts ps [tokPos l]
			   (PlainClass (Downset t)))
		<|> return (makeTypeArgs ts ps [] nullKind)
		where mergeVariance k e (t, InVar, _) p = 
			  TypeArg t e k p 
		      mergeVariance k e (t, v, ps) p =
			  TypeArg t (ExtClass e v [ps]) k p
		      makeTypeArgs ts ps q e = 
                         zipWith (mergeVariance Comma e) (init ts) 
				     (map ((:[]). tokPos) ps)
			     ++ [mergeVariance Other e (last ts) q]

-----------------------------------------------------------------------------
-- type pattern
-----------------------------------------------------------------------------

typePatternToken, primTypePatternOrId, typePatternOrId 
    :: AParser TypePattern
typePatternToken = fmap TypePatternToken (pToken (scanWords <|> placeS <|> 
				    reserved [lessS, equalS] scanSigns))

primTypePatternOrId = fmap TypePatternToken idToken 
	       <|> mkBraces typePatternOrId (BracketTypePattern Braces)
	       <|> mkBrackets typePatternOrId (BracketTypePattern Squares)
	       <|> bracketParser typePatternArgs oParenT cParenT anSemi
		       (BracketTypePattern Parens)

typePatternOrId = do ts <- many1 primTypePatternOrId
		     return( if length ts == 1 then head ts
 			     else MixfixTypePattern ts)

typePatternArgs, primTypePattern, typePattern :: AParser TypePattern
typePatternArgs = fmap TypePatternArgs typeArgs

primTypePattern = typePatternToken 
	   <|> bracketParser typePatternArgs oParenT cParenT anSemi 
		   (BracketTypePattern Parens)
	   <|> mkBraces typePattern (BracketTypePattern Braces)
           <|> mkBrackets typePatternOrId (BracketTypePattern Squares)

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

-- special pattern needed that don't contain "->" at the top-level
-- because "->" should be recognized in case-expressions

-- flag b allows "->" in patterns 

tokenPattern :: TokenMode -> AParser Pattern
tokenPattern b = fmap PatternToken (aToken b)
					  
primPattern :: TokenMode -> AParser Pattern
primPattern b = tokenPattern b 
		<|> mkBraces pattern (BracketPattern Braces) 
		<|> mkBrackets pattern (BracketPattern Squares)
		<|> bracketParser patterns oParenT cParenT anSemi 
			(BracketPattern Parens)

patterns :: AParser Pattern
patterns = do (ts, ps) <- pattern `separatedBy` anComma
	      let tp = if length ts == 1 then head ts 
		       else TuplePattern ts (map tokPos ps)
		  in return tp

mixPattern :: TokenMode -> AParser Pattern
mixPattern b = 
    do l <- many1 $ primPattern b
       let p = if length l == 1 then head l else MixfixPattern l
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
pattern = asPattern AnyToken

-----------------------------------------------------------------------------
-- instOpId
-----------------------------------------------------------------------------
-- places may follow instantiation lists

instOpId :: AParser InstOpId
instOpId = do i@(Id is cs ps) <- uninstOpId
	      if isPlace (last is) then return (InstOpId i []) 
		   else do l <- many (mkBrackets parseType Types)
			   u <- many placeT
			   return (InstOpId (Id (is++u) cs ps) l)

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
					(ps ++ toPos f cs d)
	     <|> fmap simpleTypeScheme parseType

-----------------------------------------------------------------------------
-- term
-----------------------------------------------------------------------------

tToken :: AParser Token
tToken = pToken(scanFloat <|> scanString 
		       <|> scanQuotedChar <|> scanDotWords <|> scanWords 
		       <|> scanSigns <|> placeS <?> "id/literal" )

termToken :: AParser Term
termToken = fmap TermToken (asKey exEqual <|> asKey equalS <|> tToken)

-- flag if within brackets: True allows "in"-Terms
primTerm :: TypeMode -> AParser Term
primTerm b = ifTerm b <|> termToken
	   <|> mkBraces term (BracketTerm Braces)
	   <|> mkBrackets term  (BracketTerm Squares)
 	   <|> parenTerm
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
qualOpName o = do { v <- asKey opS
		  ; i <- instOpId
 	          ; (c, t) <- partialTypeScheme
		  ; p <- cParenT
		  ; return (QualOp i t (toPos o [v, c] p))
		  }

predTypeScheme :: Pos -> TypeScheme -> TypeScheme
predTypeScheme p (TypeScheme vs (qs :=> t) ps) = 
    TypeScheme vs (qs :=> predType p t) ps

predType :: Pos -> Type -> Type
predType p t = FunType t PFunArr (BracketType Parens [] [p]) []

qualPredName :: Token -> AParser Term
qualPredName o = do { v <- asKey predS
		    ; i <- instOpId
		    ; c <- colT 
		    ; t <- typeScheme
		    ; p <- cParenT
		    ; return (QualOp i (predTypeScheme (tokPos c) t) 
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

typedTerm :: Term -> TypeMode -> AParser Term
typedTerm f b = 
    do (q, p) <- typeQual b
       t <- parseType
       return (TypedTerm f q t [tokPos p])

typedMixTerm :: TypeMode -> AParser Term
typedMixTerm b = 
    do ts <- many1 $ primTerm b
       let t = if length ts == 1 then head ts else MixfixTerm ts
	   in typedTerm t b <|> return t

-- typedMixTerm may be separated by "=" or other non-type tokens
mixTerm :: TypeMode -> AParser Term
mixTerm b = 
    do ts <- many1 $ typedMixTerm b
       return $ if length ts == 1 then head ts else MixfixTerm ts

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

exQuant :: AParser (Quantifier, Id.Token)
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
lamPattern = do (vs, ps) <- varDecls `separatedBy` anSemi
		return [PatternVars (concat vs) (map tokPos ps)]
	     <|> 
	     many (bracketParser patterns oParenT cParenT anSemi 
		      (BracketPattern Parens)) 

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
	      (ts, ps) <- patternTermPair (NoToken funS) b funS 
			  `separatedBy` barT
	      return (CaseTerm t ts (map tokPos (c:o:ps)))

-----------------------------------------------------------------------------
-- let-term
-----------------------------------------------------------------------------

letTerm :: TypeMode -> AParser Term
letTerm b = 
          do l <- asKey letS
	     (es, ps) <- patternTermPair (NoToken equalS) NoIn equalS 
			 `separatedBy` anSemi 
	     i <- asKey inS
	     t <- mixTerm b
	     return (LetTerm es t (toPos l ps i))
