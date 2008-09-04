{- |
Module      :  $Header$
Description :  parser for HasCASL kinds, types, terms, patterns and equations
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
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
import HasCASL.AsUtils
import Text.ParserCombinators.Parsec
import Data.List ((\\))
import qualified Data.Set as Set

-- * key sign tokens

-- | a colon not followed by a question mark
colT :: AParser st Token
colT = asKey colonS

-- * parser for bracketed lists

-- | a generic bracket parser
bracketParser :: AParser st a -> AParser st Token -> AParser st Token
              -> AParser st Token -> ([a] -> Range -> b) -> AParser st b
bracketParser parser op cl sep k = do
    o <- op
    (ts, ps) <- option ([], []) $ separatedBy parser sep
    c <- cl
    return $ k ts $ toRange o ps c

-- | parser for square brackets
mkBrackets :: AParser st a -> ([a] -> Range -> b) -> AParser st b
mkBrackets p c = bracketParser p oBracketT cBracketT anComma c

-- | parser for braces
mkBraces :: AParser st a -> ([a] -> Range -> b) -> AParser st b
mkBraces p c = bracketParser p oBraceT cBraceT anComma c

-- * kinds

-- | parse a simple class name or the type universe as kind
parseClassId :: AParser st Kind
parseClassId = fmap ClassKind classId

-- | do 'parseClassId' or a kind in parenthessis
parseSimpleKind :: AParser st Kind
parseSimpleKind = parseClassId <|> (oParenT >> kind << cParenT)

-- | do 'parseSimpleKind' and check for an optional 'Variance'
parseExtKind :: AParser st (Variance, Kind)
parseExtKind = bind (,) variance parseSimpleKind

-- | parse a (right associative) function kind for a given argument kind
arrowKind :: (Variance, Kind) -> AParser st Kind
arrowKind (v, k) = do
    a <- asKey funS
    k2 <- kind
    return $ FunKind v k k2 $ tokPos a

-- | parse a function kind but reject an extended kind
kind :: AParser st Kind
kind = do
    k1@(v, k) <- parseExtKind
    arrowKind k1 <|> case v of
        NonVar -> return k
        _ -> unexpected "variance of kind"

-- | parse a function kind but accept an extended kind
extKind :: AParser st (Variance, Kind)
extKind = do
    k1 <- parseExtKind
    do  k <- arrowKind k1
        return (NonVar, k)
      <|> return k1

-- * type variables

variance :: AParser st Variance
variance = let l = [CoVar, ContraVar] in
    choice (map ( \ v -> asKey (show v) >> return v) l) <|> return NonVar

-- a (simple) type variable with a 'Variance'
extVar :: AParser st Id -> AParser st (Id, Variance)
extVar vp = bind (,) vp variance

-- several 'extVar' with a 'Kind'
typeVars :: AParser st [TypeArg]
typeVars = do
    (ts, ps) <- extVar typeVar `separatedBy` anComma
    typeKind False ts ps

allIsNonVar :: [(Id, Variance)] -> Bool
allIsNonVar = all ( \ (_, v) -> case v of
    NonVar -> True
    _ -> False)

-- 'parseType' a 'Downset' starting with 'lessT' (True means require kind)
typeKind :: Bool -> [(Id, Variance)] -> [Token]
         -> AParser st [TypeArg]
typeKind b vs ps = do
    c <- colT
    if allIsNonVar vs then do
        (v, k) <- extKind
        return $ makeTypeArgs vs ps v (VarKind k) $ tokPos c
      else do
        k <- kind
        return $ makeTypeArgs vs ps NonVar (VarKind k) $ tokPos c
  <|> do
    l <- lessT
    t <- parseType
    return $ makeTypeArgs vs ps NonVar (Downset t) $ tokPos l
  <|> if b then unexpected "missing kind" else
          return (makeTypeArgs vs ps NonVar MissingKind nullRange)

-- | add the 'Kind' to all 'extVar' and yield a 'TypeArg'
makeTypeArgs :: [(Id, Variance)] -> [Token]
             -> Variance -> VarKind -> Range -> [TypeArg]
makeTypeArgs ts ps vv vk qs =
    zipWith (mergeVariance Comma vv vk) (init ts)
                (map tokPos ps)
                ++ [mergeVariance Other vv vk (last ts) qs]
                where
    mergeVariance c v k (t, NonVar) q = TypeArg t v k rStar 0 c q
    mergeVariance c _ k (t, v) q = TypeArg t v k rStar 0 c q

-- | a single 'TypeArg' (parsed by 'typeVars')
singleTypeArg :: AParser st TypeArg
singleTypeArg = do
    as <- typeVars
    case as of
      [a] -> return a
      _ -> unexpected "list of type arguments"

-- | a 'singleTypeArg' put in parentheses
parenTypeArg :: AParser st (TypeArg, [Token])
parenTypeArg = do
    o <- oParenT
    a <- singleTypeArg
    p <- cParenT
    return (a, [o, p])

-- | a 'singleTypeArg' possibly put in parentheses
typeArg :: AParser st (TypeArg, [Token])
typeArg = do
    a <- singleTypeArg
    return (a, [])
  <|> parenTypeArg

-- | a 'singleTypeArg' put in parentheses as 'TypePattern'
typePatternArg :: AParser st TypePattern
typePatternArg = do
    (a, ps) <- parenTypeArg
    return $ TypePatternArg a $ catRange ps

-- * parse special identifier tokens

type TokenMode = [String]

-- | parse a 'Token' of an 'Id' (to be declared)
-- but exclude the signs in 'TokenMode'
aToken :: TokenMode -> AParser st Token
aToken b = pToken $ scanQuotedChar <|> scanDigit <|> scanHCWords <|> placeS
    <|> reserved b scanHCSigns

-- | just 'aToken' only excluding basic HasCASL keywords
idToken :: AParser st Token
idToken = aToken [] <|> pToken scanDotWords

-- * type patterns

-- 'TypePatternToken's within 'BracketTypePattern's
-- may recusively be 'idToken's.
-- Parenthesis are only legal for a 'typePatternArg'.
primTypePatternOrId :: AParser st TypePattern
primTypePatternOrId = fmap TypePatternToken idToken
    <|> mkBraces typePatternOrId (BracketTypePattern Braces)
    <|> mkBrackets typePatternOrId (BracketTypePattern Squares)
    <|> typePatternArg

-- several 'primTypePatternOrId's possibly yielding a 'MixfixTypePattern'
mixTypePattern :: AParser st TypePattern -> AParser st TypePattern
mixTypePattern p = do
    ts <- many1 p
    return $ case ts of
       [hd] -> hd
       _ -> MixfixTypePattern ts

-- several 'primTypePatternOrId's possibly yielding a 'MixfixTypePattern'
typePatternOrId :: AParser st TypePattern
typePatternOrId = mixTypePattern primTypePatternOrId

-- | those (top-level) 'Token's (less than 'idToken')
-- that may appear in 'TypePattern's as 'TypePatternToken'.
typePatternToken :: AParser st TypePattern
typePatternToken = fmap TypePatternToken $ pToken $ scanHCWords <|> placeS
    <|> reserved hascasl_reserved_tops scanHCSigns

-- | a 'typePatternToken' or something in braces (a 'typePattern'),
-- in square brackets (a 'typePatternOrId' covering compound lists)
-- or parenthesis ('typePatternArg')
primTypePattern :: AParser st TypePattern
primTypePattern = typePatternToken
    <|> mkBrackets typePatternOrId (BracketTypePattern Squares)
    <|> mkBraces typePattern (BracketTypePattern Braces)
    <|> typePatternArg

-- several 'primTypePatter's possibly yielding a 'MixfixTypePattern'
typePattern :: AParser st TypePattern
typePattern = mixTypePattern primTypePattern

-- * types
-- a parsed type may also be interpreted as a kind (by the mixfix analysis)

-- | type tokens with some symbols removed
typeToken :: AParser st Type
typeToken = fmap TypeToken $ pToken $ scanHCWords <|> placeS <|>
    reserved (hascasl_reserved_tops ++ hascasl_type_ops)
    scanHCSigns

-- | 'TypeToken's within 'BracketType's may recusively be
-- 'idToken's. Parenthesis may group a mixfix type
-- or may be interpreted as a kind later on in a GEN-VAR-DECL.
primTypeOrId :: AParser st Type
primTypeOrId = fmap TypeToken idToken
    <|> mkBrackets typeOrId (BracketType Squares)
    <|> mkBraces typeOrId (BracketType Braces)
    <|> bracketParser typeOrId oParenT cParenT anComma (BracketType Parens)

mkMixfixType :: AParser st Type -> AParser st Type
mkMixfixType p = do
    ts <- many1 p
    return $ case ts of
              [hd] -> hd
              _ -> MixfixType ts

mkKindedMixType :: AParser st Type -> AParser st Type
mkKindedMixType p = do
    t <- mkMixfixType p
    kindAnno t <|> return t

-- | several 'primTypeOrId's possibly yielding a 'MixfixType'
-- and possibly followed by a 'kindAnno'.
typeOrId :: AParser st Type
typeOrId = mkKindedMixType primTypeOrId

-- | a 'Kind' annotation starting with 'colT'.
kindAnno :: Type -> AParser st Type
kindAnno t = do
    c <- colT
    k <- kind
    return $ KindedType t (Set.singleton k) $ tokPos c

-- | a typeToken' or a 'BracketType'. Square brackets may contain 'typeOrId'.
primType :: AParser st Type
primType = typeToken
    <|> mkBrackets typeOrId (BracketType Squares)
    <|> mkBraces parseType (BracketType Braces)
    <|> bracketParser parseType oParenT cParenT anComma (BracketType Parens)

-- | a 'primType' possibly preceded by 'quMarkT'
lazyType :: AParser st Type
lazyType = fmap mkLazyType (quMarkT >> mkMixfixType primType) <|> primType

-- | several 'lazyType's (as 'MixfixType') possibly followed by 'kindAnno'
mixType :: AParser st Type
mixType = mkKindedMixType lazyType

-- | 'mixType' possibly interspersed with 'crossT'
prodType :: AParser st Type
prodType = do
    (ts, ps) <- mixType `separatedBy` crossT
    return $ mkProductTypeWithRange ts $ catRange ps

-- | a (right associativ) function type
parseType :: AParser st Type
parseType = do
    t1 <- prodType
    do  a <- arrowT <?> funS
        t2 <- parseType
        return $ mkTypeAppl
            (TypeName a (toRaw $ funKindWithRange $ posOfId a) 0) [t1, t2]
      <|> return t1

-- | parse one of the four possible 'Arrow's
arrowT :: AParser st Id
arrowT = let l = [FunArr, PFunArr, ContFunArr, PContFunArr] in
    choice $ map ( \ a -> do
           t <- asKey $ show a
           return $ mkId [placeTok, t, placeTok]) l

-- | parse a 'TypeScheme' using 'forallT', 'typeVars', 'dotT' and 'parseType'
typeScheme :: PolyId -> AParser st TypeScheme
typeScheme (PolyId _ tys ps) = if null tys then do
    f <- forallT
    (ts, cs) <- typeVars `separatedBy` anSemi
    d <- dotT
    t <- parseType
    return $ TypeScheme (concat ts) t $ toRange f cs d
  <|> fmap simpleTypeScheme parseType
  else do
    t <- parseType
    return $ TypeScheme tys t ps

-- * varDecls and genVarDecls

-- | comma separated 'var' with 'varDeclType'
varDecls :: AParser st [VarDecl]
varDecls = do
   (vs, ps) <- var `separatedBy` anComma
   varDeclType vs ps

-- | a type ('parseType') following a colon
varDeclType :: [Id] -> [Token] -> AParser st [VarDecl]
varDeclType vs ps = do
    c <- colonST
    t <- parseType
    return $ makeVarDecls vs ps t $ tokPos c

-- | attach the 'Type' to every 'Var'
makeVarDecls :: [Id] -> [Token] -> Type -> Range -> [VarDecl]
makeVarDecls vs ps t q = zipWith ( \ v p -> VarDecl v t Comma $ tokPos p)
    (init vs) ps ++ [VarDecl (last vs) t Other q]

-- | either like 'varDecls' or declared type variables.
-- A 'GenVarDecl' may later become a 'GenTypeVarDecl'.
genVarDecls:: AParser st [GenVarDecl]
genVarDecls = fmap (map ( \ g -> case g of
    GenTypeVarDecl (TypeArg i v MissingKind _ n s ps) ->
        GenTypeVarDecl (TypeArg i v (VarKind universe)
                                              rStar n s ps)
    _ -> g)) $ do
    (vs, ps) <- extVar var `separatedBy` anComma
    let other = fmap (map GenTypeVarDecl) (typeKind True vs ps)
    if allIsNonVar vs then fmap (map GenVarDecl)
        (varDeclType (map ( \ (i, _) -> i) vs) ps) <|> other
      else other

-- * patterns

{- | different legal 'TermToken's possibly excluding 'funS' or
'equalS' for case or let patterns resp. -}
tokenPattern :: TokenMode -> AParser st Term
tokenPattern b = fmap TermToken (aToken b <|> pToken (string "_"))
-- a single underscore serves as wildcard pattern

-- | 'tokenPattern' or 'BracketTerm'
primPattern :: TokenMode -> AParser st Term
primPattern b = tokenPattern b
    <|> mkBrackets pattern (BracketTerm Squares)
    <|> mkBraces pattern (BracketTerm Braces)
    <|> bracketParser (pattern <|> varTerm <|> qualOpName)
          oParenT cParenT anComma (BracketTerm Parens)

mkMixfixTerm :: [Term] -> Term
mkMixfixTerm ts = case ts of
    [hd] -> hd
    _ -> MixfixTerm ts

-- | several 'typedPattern'
mixPattern :: TokenMode -> AParser st Term
mixPattern = fmap mkMixfixTerm . many1 . asPattern

-- | a possibly typed ('parseType') pattern
typedPattern :: TokenMode -> AParser st Term
typedPattern b = do
    t <- primPattern b
    do  c <- colT
        ty <- parseType
        return $ MixfixTerm [t, MixTypeTerm OfType ty $ tokPos c]
      <|> return t

-- | top-level pattern (possibly 'AsPattern')
asPattern :: TokenMode -> AParser st Term
asPattern b = do
    v <- typedPattern b
    case v of
      TermToken tt -> if isPlace tt then return v else do
          c <- asKey asP
          t <- typedPattern b
          return $ AsPattern (VarDecl (mkId [tt]) (MixfixType [])
                              Other $ tokPos c) t $ tokPos c
        <|> return v
      _ -> return v

-- | an unrestricted 'asPattern'
pattern :: AParser st Term
pattern = mixPattern []

myChoice :: [(AParser st Token, a)] -> AParser st (a, Token)
myChoice = choice . map ( \ (p, a) -> do
   t <- p
   return (a, t))

-- | a 'Total' or 'Partial' lambda dot
lamDot :: AParser st (Partiality, Token)
lamDot = myChoice [ (choice $ map (asKey . (++ exMark)) [dotS, cDot], Total)
                  , (dotT, Partial)]

-- | patterns between 'lamS' and 'lamDot'
lamPattern :: AParser st [Term]
lamPattern =
    (lookAhead lamDot >> return []) <|> bind (:) (typedPattern []) lamPattern

-- * terms

{- | 'Token's that may occur in 'Term's including literals
   'scanFloat', 'scanString' but excluding 'ifS', 'whenS' and 'elseS'
   to allow a quantifier after 'whenS'. In case-terms also 'barS' will
   be excluded on the top-level. -}

tToken :: TokenMode -> AParser st Token
tToken b = pToken (scanFloat
    <|> scanString
    <|> scanQuotedChar <|> scanDotWords
    <|> reserved [ifS, whenS, elseS] scanHCWords
    <|> reserved b scanHCSigns
    <|> placeS <?> "id/literal")

-- | 'tToken' as 'Term' plus 'exEqual' and 'equalS'
termToken :: TokenMode -> AParser st Term
termToken b = fmap TermToken (asKey exEqual <|> asKey equalS <|> tToken b)

-- | 'termToken' plus 'BracketTerm's
primTerm :: TokenMode -> AParser st Term
primTerm b = termToken b
    <|> mkBraces term (BracketTerm Braces)
    <|> mkBrackets term (BracketTerm Squares)
    <|> bracketParser termInParens oParenT cParenT anComma (BracketTerm Parens)

-- | how the keyword 'inS' should be treated
data InMode = NoIn   -- ^ next 'inS' belongs to 'letS'
            | WithIn -- ^ 'inS' is the element test

-- | all 'Term's that start with a unique keyword
baseTerm :: (InMode, TokenMode) -> AParser st Term
baseTerm b = ifTerm b
    <|> whenTerm b
    <|> forallTerm b
    <|> exTerm b
    <|> lambdaTerm b
    <|> caseTerm b
    <|> letTerm b

-- | 'whenS' possibly followed by an 'elseS'
whenTerm :: (InMode, TokenMode) -> AParser st Term
whenTerm b = do
    i <- asKey whenS
    c <- mixTerm b
    let l1 = [TermToken i, c]
    do  t <- asKey elseS
        e <- mixTerm b
        return $ MixfixTerm $ l1 ++ [TermToken t, e]
      <|> return (MixfixTerm l1)

-- | 'ifS' possibly followed by 'thenS' and 'elseS'
-- yielding a 'MixfixTerm'
ifTerm :: (InMode, TokenMode) -> AParser st Term
ifTerm b = do
    i <- asKey ifS
    c <- mixTerm b
    let l1 = [TermToken i, c]
    do  t <- asKey thenS
        e <- mixTerm b
        let l2 = l1 ++ [TermToken t, e]
        do  s <- asKey elseS
            f <- mixTerm b
            return $ MixfixTerm $ l2 ++ [TermToken s, f]
          <|> return (MixfixTerm l2)
      <|> return (MixfixTerm l1)

-- | unrestricted terms including qualified names
termInParens :: AParser st Term
termInParens = term <|> varTerm <|> qualOpName <|> qualPredName

-- | a qualified 'var'
varTerm :: AParser st Term
varTerm = do
    v <- asKey varS
    i <- var
    c <- colonST
    t <- parseType
    return $ QualVar $ VarDecl i t Other $ toRange v [] c

-- | 'opS' or 'functS'
opBrand :: AParser st (Token, OpBrand)
opBrand = bind (,) (asKey opS) (return Op)
    <|> bind (,) (asKey functS) (return Fun)

parsePolyId :: AParser st PolyId
parsePolyId = do
    l <- try ite <|> start hcKeys
    if isPlace (last l)
      then return $ PolyId (Id l [] nullRange) [] nullRange else do
        (cs, ps) <- option ([], nullRange) (try $ comps hcKeys)
        (tys, qs) <- option ([], nullRange) $
                bracketParser typeVars oBracketT cBracketT semiT (,)
        u <- many placeT
        return $ PolyId (Id (l ++ u) cs ps) (concat tys) qs

-- | a qualified operation (with 'opBrand')
qualOpName :: AParser st Term
qualOpName = do
    (v, b) <- opBrand
    i <- parsePolyId
    c <- colonST
    t <- typeScheme i
    return $ QualOp b i t [] Infer $ toRange v [] c

-- | a qualified predicate
qualPredName :: AParser st Term
qualPredName = do
    v <- asKey predS
    i <- parsePolyId
    c <- colT
    t <- typeScheme i
    let p = toRange v [] c
    return $ QualOp Pred i (predTypeScheme p t) [] Infer p

-- | a qualifier expecting a further 'Type'.
-- 'inS' is rejected for 'NoIn'
typeQual :: InMode -> AParser st (TypeQual, Token)
typeQual m = myChoice $ (colT, OfType) : (asT, AsType) : case m of
    NoIn -> []
    WithIn -> [(asKey inS, InType)]

-- | a possibly type qualified ('typeQual') 'primTerm' or a 'baseTerm'
typedTerm :: (InMode, TokenMode) -> AParser st Term
typedTerm (i, b) = do
    t <- primTerm b
    do  (q, p) <- typeQual i
        ty <- parseType
        return $ MixfixTerm [t, MixTypeTerm q ty $ tokPos p]
      <|> return t
  <|> baseTerm (i, b)

-- | several 'typedTerm's yielding a 'MixfixTerm'
mixTerm :: (InMode, TokenMode) -> AParser st Term
mixTerm = fmap mkMixfixTerm . many1 . typedTerm

-- | keywords that start a new item
hasCaslStartKeywords :: [String]
hasCaslStartKeywords =
    dotS : cDot : (hascasl_reserved_words \\ [existsS, letS, caseS])

-- | a 'mixTerm' followed by 'whereS' and equations separated by 'optSemi'
whereTerm :: (InMode, TokenMode) -> AParser st Term
whereTerm b = do
    t <- mixTerm b
    do  p <- asKey whereS
        (es, ps, _ans) <- itemAux hasCaslStartKeywords $
          patternTermPair [equalS] b equalS
          -- ignore collected annotations
        return $ LetTerm Where es t $ catRange $ p : ps
      <|> return t

-- | a 'whereTerm' called with ('WithIn', [])
term :: AParser st Term
term = whereTerm (WithIn, [])

-- | a 'Universal' 'QuantifiedTerm'
forallTerm :: (InMode, TokenMode) -> AParser st Term
forallTerm b = do
    f <- forallT
    (vs, ps) <- genVarDecls `separatedBy` anSemi
    addAnnos
    d <- dotT
    t <- mixTerm b
    return $ QuantifiedTerm Universal (concat vs) t $ toRange f ps d

-- | 'Unique' or 'Existential'
exQuant :: AParser st (Token, Quantifier)
exQuant = bind (,) (asKey (existsS++exMark)) (return Unique)
    <|> bind (,) (asKey existsS) (return Existential)

-- | a (possibly unique) existential 'QuantifiedTerm'
exTerm :: (InMode, TokenMode) -> AParser st Term
exTerm b = do
    (p, q) <- exQuant <?> existsS
    (vs, ps) <- varDecls `separatedBy` anSemi
    d <- dotT
    f <- mixTerm b
    return $ QuantifiedTerm q (map GenVarDecl (concat vs)) f $ toRange p ps d

lamDecls :: AParser st [Term]
lamDecls = try ((do
    (vs, _) <- separatedBy varDecls anSemi
    lookAhead lamDot
    return $ case concat vs of
      [(VarDecl (Id [t] [] _) ty _ ps)] ->
          -- this may be a constant constructor
          [MixfixTerm [TermToken t, MixTypeTerm OfType ty ps]]
      vss -> map QualVar vss) <?> "VAR-DECL") <|> lamPattern

-- | a 'LambdaTerm'
lambdaTerm :: (InMode, TokenMode) -> AParser st Term
lambdaTerm b = do
    l <- asKey lamS
    pl <- lamDecls
    (k, d) <- lamDot
    t <- mixTerm b
    return $ LambdaTerm (if null pl then [BracketTerm Parens [] nullRange]
                         else pl) k t $ toRange l [] d

-- | a 'CaseTerm' with 'funS' excluded in 'patternTermPair'
caseTerm :: (InMode, TokenMode) -> AParser st Term
caseTerm (i, _) = do
    c <- asKey caseS
    t <- term
    o <- asKey ofS
    (ts, ps) <- patternTermPair [funS] (i, [barS]) funS `separatedBy` barT
    return $ CaseTerm t ts $ catRange $ c : o : ps

-- | a 'LetTerm' with 'equalS' excluded in 'patternTermPair'
-- (called with 'NoIn')
letTerm :: (InMode, TokenMode) -> AParser st Term
letTerm b = do
    l <- asKey letS
    (es, ps) <- patternTermPair [equalS] (NoIn, []) equalS `separatedBy` anSemi
    i <- asKey inS
    t <- mixTerm b
    return $ LetTerm Let es t $ toRange l ps i

-- | a customizable pattern equation
patternTermPair :: TokenMode -> (InMode, TokenMode) -> String
                -> AParser st ProgEq
patternTermPair b1 b2 sep = do
    p <- mixPattern b1
    s <- asKey sep
    t <- mixTerm b2
    return $ ProgEq p t $ tokPos s
