
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
   
   parser for HasCASL kinds, types, terms, patterns and equations
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
import Data.List

-- * key sign tokens

-- | keywords for the variance of kinds  
plusT, minusT :: AParser Token
plusT = asKey plusS
minusT = asKey minusS

-- | a keyword string not followed by a question mark
noQuMark :: String -> AParser Token
noQuMark s = try $ asKey s << notFollowedBy (char '?')

-- | a colon not followed by a question mark
colT :: AParser Token
colT = noQuMark colonS

-- | a colon immediately followed by a question mark
qColonT :: AParser Token
qColonT = asKey (colonS++quMark)

-- * parser for bracketed lists

-- | a generic bracket parser 
bracketParser :: AParser a -> AParser Token -> AParser Token -> AParser Token 
	 -> ([a] -> [Pos] -> b) -> AParser b
bracketParser parser op cl sep k = 
    do o <- op
       (ts, ps) <- option ([], []) (parser `separatedBy` sep)
       c <- cl
       return (k ts (toPos o ps c))

-- | parser for square brackets
mkBrackets :: AParser a -> ([a] -> [Pos] -> b) -> AParser b
mkBrackets p c = bracketParser p oBracketT cBracketT anComma c

-- | parser for braces
mkBraces :: AParser a -> ([a] -> [Pos] -> b) -> AParser b
mkBraces p c = bracketParser p oBraceT cBraceT anComma c

-- * kinds

-- | parse a simple class name or the type universe as kind
parseClassId :: AParser Kind
parseClassId = fmap (\c -> if showId c "" == "Type" 
		   then Universe [posOfId c]
		   else ClassKind c MissingKind) classId

-- | do 'parseClassId' or a downset or an intersection kind 
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
	        i <- pToken scanHCWords
		d <- dotT
		j <- asKey (tokStr i)
		l <- lessT
		t <- parseType
		p <- cBraceT
		return (Downset (Just i) t MissingKind 
			(map tokPos [o,d,j,l,p])) 

-- | do 'parseSimpleKind' and check for an optional 'Variance'
parseExtKind :: AParser Kind
parseExtKind = do k <- parseSimpleKind
	          do s <- plusT
		     return (ExtKind k CoVar [tokPos s])
                   <|>
		   do m <- minusT
		      return (ExtKind k ContraVar [tokPos m])
                   <|> return k

-- | parse a (right associative) function kind for a given argument kind
arrowKind :: Kind -> AParser Kind
arrowKind k1 =
       do a <- asKey funS
	  k2 <- kind
	  return (FunKind k1 k2 $ [tokPos a])

-- | parse a function kind but reject an extended kind
kind :: AParser Kind
kind = 
    do k1 <- parseExtKind
       arrowKind k1 <|> case k1 of
	    ExtKind _ CoVar _ -> unexpected "co-variance of kind"
	    ExtKind _ ContraVar _ -> unexpected "contra-variance of kind"
	    ExtKind k InVar _  -> return k
	    _ -> return k1

-- | parse a function kind but accept an extended kind
extKind :: AParser Kind
extKind = 
    do k1 <- parseExtKind
       arrowKind k1 <|> return k1


-- * type variables

-- a (simple) type variable with a 'Variance'
extVar :: AParser Id -> AParser (Id, Variance, Pos) 
extVar vp = 
    do t <- vp
       do   a <- plusT
	    return (t, CoVar, tokPos a)
          <|>
	  do a <- minusT
	     return (t, ContraVar, tokPos a)
          <|> return (t, InVar, nullPos)

-- several 'extTypeVar' with a 'Kind'
typeVars :: AParser [TypeArg]
typeVars = do (ts, ps) <- extVar typeVar `separatedBy` anComma
	      typeKind ts ps

allIsInVar :: [(TypeId, Variance, Pos)] -> Bool
allIsInVar = all ( \ (_, v, _) -> case v of InVar -> True 
		                            _ -> False)   

-- 'parseType' a 'Downset' starting with 'lessT'
typeKind :: [(TypeId, Variance, Pos)] -> [Token] -> AParser [TypeArg]
typeKind vs ps = 
    do c <- colT
       if allIsInVar vs then 
	  do k <- extKind
	     return (makeTypeArgs vs ps [tokPos c] k)
          else do k <- kind
		  return (makeTypeArgs vs ps [tokPos c] k)
    <|>
    do l <- lessT
       t <- parseType
       return (makeTypeArgs vs ps [tokPos l]
		  (Downset Nothing t MissingKind [])) 
    <|> return (makeTypeArgs vs ps [] star)

-- | add the 'Kind' to all 'extTypeVar' and yield a 'TypeArg'
makeTypeArgs :: [(TypeId, Variance, Pos)] -> [Token] 
	     -> [Pos] -> Kind -> [TypeArg]
makeTypeArgs ts ps qs k = 
    zipWith (mergeVariance Comma k) (init ts) 
		(map ((:[]). tokPos) ps)
		++ [mergeVariance Other k (last ts) qs]
		where mergeVariance c e (t, InVar, _) q =
			  TypeArg t e c q
		      mergeVariance c e (t, v, p) q = 
			  TypeArg t (ExtKind e v [p]) c q 

-- | a single 'TypeArg' (parsed by 'typeVars')
singleTypeArg :: AParser TypeArg
singleTypeArg = do  as <- typeVars
		    case as of 
			    [a] -> return a 
			    _ -> unexpected "list of type arguments"

-- | a 'singleTypArg' put in parentheses
parenTypeArg :: AParser (TypeArg, [Token])
parenTypeArg = 
    do o <- oParenT
       a <- singleTypeArg
       p <- cParenT
       return (a, [o, p])

-- | a 'singleTypeArg' possibly put in parentheses
typeArg :: AParser (TypeArg, [Token])
typeArg = 
    do a <- singleTypeArg
       return (a, [])
     <|> parenTypeArg

-- | several 'typeArg's 
typeArgs :: AParser ([TypeArg], [Token])
typeArgs = 
    do l <- many1 typeArg
       return (map fst l, concatMap snd l)

-- | a 'singleTypeArg' put in parentheses as 'TypePattern'
typePatternArg :: AParser TypePattern
typePatternArg = 
    do (a, ps) <- parenTypeArg
       return $ TypePatternArg a $ map tokPos ps

-- * parse special identifier tokens

type TokenMode = [String]   

-- | parse a 'Token' of an 'Id' (to be declared) 
-- but exclude the signs in 'TokenMode'
aToken :: TokenMode -> AParser Token
aToken b = pToken (scanQuotedChar <|> scanDotWords 
		   <|> scanDigit <|> scanHCWords <|> placeS <|> 
		   reserved b scanHCSigns)

-- | just 'aToken' only excluding basic HasCASL keywords
idToken :: AParser Token
idToken = aToken []

-- * type patterns

-- 'TypePatternToken's within 'BracketTypePattern's 
-- may recusively be 'idToken's.
-- Parenthesis are only legal for a 'typePatternArg'.
primTypePatternOrId :: AParser TypePattern
primTypePatternOrId = fmap TypePatternToken idToken 
	       <|> mkBraces typePatternOrId (BracketTypePattern Braces)
	       <|> mkBrackets typePatternOrId (BracketTypePattern Squares)
	       <|> typePatternArg

-- several 'primTypePatternOrId's possibly yielding a 'MixfixTypePattern'
typePatternOrId :: AParser TypePattern
typePatternOrId = do ts <- many1 primTypePatternOrId
		     return( if isSingle ts then head ts
 			     else MixfixTypePattern ts)

-- | those (top-level) 'Token's (less than 'idToken') 
-- that may appear in 'TypePattern's as 'TypePatternToken'.
typePatternToken :: AParser TypePattern
typePatternToken = fmap TypePatternToken (pToken (scanHCWords <|> placeS <|> 
				    reserved [lessS, equalS] scanHCSigns))

-- | a 'typePatternToken' or something in braces (a 'typePattern'),
-- in square brackets (a 'typePatternOrId' covering compound lists) 
-- or parenthesis ('typePatternArg')
primTypePattern :: AParser TypePattern
primTypePattern = typePatternToken 
	   <|> typePatternArg
	   <|> mkBraces typePattern (BracketTypePattern Braces)
           <|> mkBrackets typePatternOrId (BracketTypePattern Squares)


-- several 'primTypePatter's possibly yielding a 'MixfixTypePattern'
typePattern :: AParser TypePattern
typePattern = do ts <- many1 primTypePattern
                 let t = if isSingle ts then head ts 
			 else MixfixTypePattern ts
	           in return t

-- * types 
-- a parsed type may also be interpreted as a kind (by the mixfix analysis)

-- | type tokens with some symbols removed
typeToken :: AParser Type
typeToken = fmap TypeToken (pToken (scanHCWords <|> placeS <|> 
				    reserved (lessS : equalS : barS :
					      hascasl_type_ops 
					      ++ hascasl_reserved_ops)
				    scanHCSigns))


-- | 'TypeToken's within 'BracketType's may recusively be
-- 'idToken's. Parenthesis may group a mixfix type 
-- or may be interpreted as 'Intersection' later in a GEN-VAR-DECL.
primTypeOrId :: AParser Type
primTypeOrId = fmap TypeToken idToken
	       <|> mkBraces typeOrId (BracketType Braces)
	       <|> mkBrackets typeOrId (BracketType Squares)
	       <|> bracketParser typeOrId oParenT cParenT anComma
		       (BracketType Parens)
	       
-- | several 'primTypeOrId's possibly yielding a 'MixfixType' 
-- and possibly followed by a 'kindAnno'.
typeOrId :: AParser Type
typeOrId = do ts <- many1 primTypeOrId
	      let t = if isSingle ts then head ts
 		      else MixfixType ts
		 in 
		 kindAnno t
 		 <|> 
		 return(t)

-- | a 'Kind' annotation starting with 'colT'.
kindAnno :: Type -> AParser Type
kindAnno t = do c <- colT 
		k <- kind
		return (KindedType t k [tokPos c])

-- | a typeToken' or a 'BracketType'. Square brackets may contain 'typeOrId'.
primType :: AParser Type
primType = typeToken 
	   <|> bracketParser parseType oParenT cParenT anComma 
		   (BracketType Parens)
	   <|> mkBraces parseType (BracketType Braces)
           <|> mkBrackets typeOrId (BracketType Squares)

-- | a 'primType' possibly preceded by 'quMarkT'
lazyType :: AParser Type
lazyType = do q <- quMarkT
	      t <- primType 
              return (LazyType t [tokPos q])
	   <|> primType

-- | several 'lazyType's (as 'MixfixType') possibly followed by 'kindAnno' 
mixType :: AParser Type
mixType = do ts <- many1 lazyType
             let t = if isSingle ts then head ts else MixfixType ts
	       in kindAnno t
		  <|> return t 

-- | 'mixType' possibly interspersed with 'crossT' 
prodType :: AParser Type
prodType = do (ts, ps) <- mixType `separatedBy` crossT
	      return $ mkProductType ts (map tokPos ps)

-- | a (right associativ) function type  
parseType :: AParser Type
parseType = 
    do t1 <- prodType 
       do a <- arrowT
	  t2 <- parseType
	  return $ FunType t1 (fst a) t2 [snd a] 
        <|> return t1

-- | parse one of the four possible 'Arrow's
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

-- | parse a 'TypeScheme' using 'forallT', 'typeVars', 'dotT' and 'parseType'
typeScheme :: AParser TypeScheme
typeScheme = do f <- forallT
		(ts, cs) <- typeVars `separatedBy` anSemi
		d <- dotT
		t <- typeScheme
                return $ case t of 
			 TypeScheme ots q ps ->
			     TypeScheme (concat ts ++ ots) q 
					(toPos f cs d ++ ps)
	     <|> fmap simpleTypeScheme parseType

-- a 'TypeScheme' for a possibly partial constant (given by 'qColonT')
partialTypeScheme :: AParser (Token, TypeScheme)
partialTypeScheme = do q <- qColonT
		       t <- parseType 
		       return (q, simpleTypeScheme 
			       (FunType (BracketType Parens [] [tokPos q]) 
				PFunArr t [tokPos q]))
		    <|> bind (,) colT typeScheme

-- * varDecls and genVarDecls

-- | comma separated 'var' with 'varDeclType'
varDecls :: AParser [VarDecl]
varDecls = do (vs, ps) <- var `separatedBy` anComma
	      varDeclType vs ps

-- | a type ('parseType') following a 'colT' 
varDeclType :: [Var] -> [Token] -> AParser [VarDecl]
varDeclType vs ps = do c <- colT
		       t <- parseType
		       return (makeVarDecls vs ps t (tokPos c))

-- | attach the 'Type' to every 'Var'
makeVarDecls :: [Var] -> [Token] -> Type -> Pos -> [VarDecl]
makeVarDecls vs ps t q = zipWith (\ v p -> VarDecl v t Comma [tokPos p])
		     (init vs) ps ++ [VarDecl (last vs) t Other [q]]

-- | either like 'varDecls' or type variables with a 'typeDownset'.
-- A 'GenVarDecl' may later become a 'GenTypeVarDecl'.
genVarDecls:: AParser [GenVarDecl]
genVarDecls = do (vs, ps) <- extVar var `separatedBy` anComma
		 if allIsInVar vs then
		    fmap (map GenVarDecl) 
			     (varDeclType 
			      (map ( \ (i, _, _) -> i) vs) ps)
		      <|> fmap (map GenTypeVarDecl)
			       (typeKind vs ps)
		     else fmap (map GenTypeVarDecl)
			       (typeKind vs ps)

-- * patterns

-- | different legal 'PatternToken's (in- or excluding 'funS')
tokenPattern :: TokenMode -> AParser Pattern
tokenPattern b = fmap PatternToken (aToken b)
					  
-- | 'tokenPattern' or 'BracketPattern'
primPattern :: TokenMode -> AParser Pattern
primPattern b = tokenPattern b 
		<|> mkBraces pattern (BracketPattern Braces) 
		<|> mkBrackets pattern (BracketPattern Squares)
		<|> bracketParser pattern oParenT cParenT anComma
			(BracketPattern Parens)

-- | several 'primPattern' possibly with a 'typeAnno'
mixPattern :: TokenMode -> AParser Pattern
mixPattern b = 
    do l <- many1 $ primPattern b
       let p = if isSingle l then head l else MixfixPattern l
	   in typeAnno p <|> return p

-- | a type ('parseType') preceded by 'colT'
typeAnno :: Pattern -> AParser Pattern
typeAnno p = 
    do c <- colT
       t <- parseType
       return $ TypedPattern p t [tokPos c]

-- | top-level pattern (possibly 'AsPattern')
asPattern :: TokenMode -> AParser Pattern
asPattern b = 
    do v <- mixPattern b
       do   c <- asKey asP 
	    t <- mixPattern b 
	    case v of PatternToken _ -> return (AsPattern v t [tokPos c])
		      _ -> unexpected "complex pattern before '@'"    
         <|> return v

-- | an unrestricted 'asPattern'
pattern :: AParser Pattern
pattern = asPattern []

-- | a 'Total' or 'Partial' lambda dot
lamDot :: AParser (Partiality, Token)
lamDot = do d <- asKey (dotS++exMark) <|> asKey (cDot++exMark)
	    return (Total,d)
	 <|> 
	 do d <- dotT
	    return (Partial,d)

-- | patterns between 'lamS' and 'lamDot'
lamPattern :: AParser [Pattern]
lamPattern = 
    do  lookAhead lamDot 
	return []
      <|> do p <- pattern
	     ps <- lamPattern
	     return (p : ps)

-- * terms

-- | an 'uninstOpId' possibly followed by types ('parseType') in brackets 
-- and further places ('placeT')
instOpId :: AParser InstOpId
instOpId = do i@(Id is cs ps) <- uninstOpId
	      if isPlace (last is) then return (InstOpId i [] []) 
		   else do (ts, qs) <- option ([], [])
				       (mkBrackets parseType (,))
			   u <- many placeT
			   return (InstOpId (Id (is++u) cs ps) ts qs)

-- | 'Token's that may occur in 'Term's including literals 
-- ('scanFloat', 'scanString') excluding 'ifS' and 'barS'
tToken :: TokenMode -> AParser Token
tToken b = pToken(scanFloat <|> scanString 
		<|> scanQuotedChar <|> scanDotWords 
		<|> reserved [ifS] scanHCWords 
		<|> reserved b scanHCSigns 
		<|> placeS <?> "id/literal" )


-- | 'tToken' as 'Term' plus 'exEqual' and 'equalS'
termToken :: TokenMode -> AParser Term
termToken b = fmap TermToken (asKey exEqual <|> asKey equalS <|> tToken b)

-- | 'termToken' plus 'BracketTerm's or 'parenTerm'
primTerm :: TokenMode -> AParser Term
primTerm b = termToken b
	   <|> mkBraces term (BracketTerm Braces)
	   <|> mkBrackets term (BracketTerm Squares)
 	   <|> parenTerm

-- | how the keyword 'inS' should be treated  
data InMode = NoIn   -- ^ next 'inS' belongs to 'letS' 
            | WithIn -- ^ 'inS' is the element test 

-- | all 'Term's that start with a unique keyword
baseTerm :: (InMode, TokenMode) -> AParser Term
baseTerm b = ifTerm b
           <|> forallTerm b 
	   <|> exTerm b 
	   <|> lambdaTerm b 
	   <|> caseTerm b
	   <|> letTerm b

-- | 'ifS' possibly followed by 'thenS' (for if-then-else) 
-- yielding a 'MixfixTerm'.
ifTerm :: (InMode, TokenMode) -> AParser Term
ifTerm b = 
    do i <- asKey ifS
       c <- mixTerm b
       do t <- asKey thenS
	  e <- mixTerm b
	  return (MixfixTerm [TermToken i, c, TermToken t, e])
	<|> return (MixfixTerm [TermToken i, c])

-- | a 'Term' in parentheses, may be a qualified name or a tuple 
-- ('BracketTerm')
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
		     		
-- | a qualified 'var'
varTerm :: Token -> AParser Term
varTerm o = do v <- asKey varS
	       i <- var
	       c <- colT
	       t <- parseType
	       p <- cParenT
	       return (QualVar i t (toPos o [v, c] p))

-- | 'opS' or 'functS'
opBrand :: AParser (Token, OpBrand)
opBrand = bind (,) (asKey opS) (return Op)
	  <|> bind (,) (asKey functS) (return Fun) 

-- | a qualified operation (with 'opBrand') 
qualOpName :: Token -> AParser Term
qualOpName o = 
    do (v, b) <- opBrand
       i <- instOpId
       (c, t) <- partialTypeScheme
       p <- cParenT
       return $ QualOp b i t (toPos o [v, c] p)

-- | a qualified predicate
qualPredName :: Token -> AParser Term
qualPredName o = 
    do v <- asKey predS
       i <- instOpId
       c <- colT 
       t <- typeScheme
       p <- cParenT
       return $ QualOp Pred i (predTypeScheme t) (toPos o [v, c] p)


-- | a qualifier expecting a further 'Type'. 
-- 'inS' is rejected for 'NoIn'
typeQual :: InMode -> AParser (TypeQual, Token) 
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

-- | a possibly type qualified ('typeQual') 'primTerm' or a 'baseTerm' 
typedTerm :: (InMode, TokenMode) -> AParser Term
typedTerm (i, b) = 
    do t <- primTerm b
       do (q, p) <- typeQual i
	  ty <- parseType
	  return (case q of 
			  InType -> MixfixTerm [t, MixInTerm ty [tokPos p]]
			  _ -> TypedTerm t q ty [tokPos p])
        <|> return t
      <|> baseTerm (i, b)

-- | several 'typedTerm's yielding a 'MixfixTerm'
mixTerm :: (InMode, TokenMode) -> AParser Term
mixTerm b = 
    do ts <- many1 $ typedTerm b
       return $ if isSingle ts then head ts else MixfixTerm ts

-- | keywords that start a new item 
hasCaslStartKeywords :: [String]
hasCaslStartKeywords = 
    dotS:cDot: (hascasl_reserved_words \\ [existsS, letS, caseS])

-- | a 'mixTerm' followed by 'whereS' and equations separated by 'optSemi'
whereTerm :: (InMode, TokenMode) -> AParser Term
whereTerm b = 
    do t <- mixTerm b 
       do p <- asKey whereS
	  (es, ps, ans) <- itemAux hasCaslStartKeywords $
			   patternTermPair ([equalS]) b equalS 
          setState (AnnoState (concat ans)) -- store back collected annotations
	  return (LetTerm Where es t (map tokPos (p:ps)))
        <|> return t

-- | a 'whereTerm' called with ('WithIn', [])
term :: AParser Term
term = whereTerm (WithIn, [])

-- | a 'Universal' 'QuantifiedTerm'
forallTerm :: (InMode, TokenMode) -> AParser Term
forallTerm b = 
    do f <- forallT
       (vs, ps) <- genVarDecls `separatedBy` anSemi
       addAnnos
       d <- dotT
       t <- mixTerm b
       return $ QuantifiedTerm Universal (concat vs) t $ toPos f ps d

-- | 'Unique' or 'Existential'
exQuant :: AParser (Token, Quantifier)
exQuant =
    bind (,) (asKey (existsS++exMark)) (return Unique)
             <|> bind (,) (asKey existsS) (return Existential)

-- | a (possibly unique) existential 'QuantifiedTerm'
exTerm :: (InMode, TokenMode) -> AParser Term
exTerm b = 
    do (p, q) <- exQuant
       (vs, ps) <- varDecls `separatedBy` anSemi
       d <- dotT
       f <- mixTerm b
       return $ QuantifiedTerm q (map GenVarDecl (concat vs)) f $ toPos p ps d


-- | a 'LambdaTerm'
lambdaTerm :: (InMode, TokenMode) -> AParser Term
lambdaTerm b = 
             do l <- asKey lamS
		pl <- lamPattern
		(k, d) <- lamDot      
		t <- mixTerm b
		return (LambdaTerm pl k t (toPos l [] d))

-- | a 'CaseTerm' with 'funS' excluded in 'patternTermPair'
caseTerm :: (InMode, TokenMode) -> AParser Term
caseTerm (i, _) = 
           do c <- asKey caseS
	      t <- term
	      o <- asKey ofS
	      (ts, ps) <- patternTermPair [funS] (i, [barS]) funS 
			  `separatedBy` barT
	      return (CaseTerm t ts (map tokPos (c:o:ps)))

-- | a 'LetTerm' with 'equalS' excluded in 'patternTermPair' 
-- (called with 'NoIn')
letTerm :: (InMode, TokenMode) -> AParser Term
letTerm b = 
          do l <- asKey letS
	     (es, ps) <- patternTermPair [equalS] (NoIn, []) equalS 
			 `separatedBy` anSemi 
	     i <- asKey inS
	     t <- mixTerm b
	     return (LetTerm Let es t (toPos l ps i))

-- | a customizable pattern equation 
patternTermPair :: TokenMode -> (InMode, TokenMode) -> String -> AParser ProgEq
patternTermPair b1 b2 sep = 
    do p <- asPattern b1
       s <- asKey sep
       t <- mixTerm b2
       return (ProgEq p t (tokPos s))
