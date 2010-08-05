{- |
Module      :  $Header$
Description :  ADL syntax parser
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.Parse where

import Adl.As

import Common.Id
import Common.Lexer (parseToken)
import Common.Parsec
import Common.Token (casl_structured_reserved_words)
import Control.Monad
import Text.ParserCombinators.Parsec

keywordstxt :: [String]
keywordstxt =
  [ "CONTEXT", "ENDCONTEXT", "EXTENDS"
  , "PATTERN", "ENDPATTERN"
  , "SERVICE", "INITIAL", "SQLPLUG", "PHPPLUG"
  , "POPULATION", "CONTAINS"
  , "UNI", "INJ", "SUR", "TOT", "SYM", "ASY", "TRN", "RFX", "PROP", "ALWAYS"
  , "RULE", "MAINTAINS", "SIGNALS", "SIGNAL", "ON"
  , "RELATION", "CONCEPT", "KEY"
  , "IMPORT", "GEN", "ISA", "I", "V", "S"
  , "PRAGMA", "EXPLANATION", "EXPLAIN", "IN", "REF", "ENGLISH", "DUTCH"
  , "ONE", "BIND", "TOPHP", "BINDING"
  ]

-- | a line comment starts with --. In haskell this may be part of an operator.
lineComment :: CharParser st String
lineComment = tryString "--" <++> many (noneOf "\n")

skip :: CharParser st ()
skip = skipMany $ forget space
  <|> forget (nestedComment "{-" "-}" <|> lineComment)

pChar :: CharParser st Char
pChar = alphaNum <|> oneOf "_'"

pKeyS :: String -> CharParser st String
pKeyS s = try (string s << notFollowedBy pChar) << skip

pKey :: String -> CharParser st ()
pKey = forget . pKeyS

pSymC :: String -> String -> CharParser st String
pSymC s cs = try (string s << notFollowedBy (oneOf cs)) << skip

-- do not parse a double colon
pColon :: CharParser st String
pColon = pSymC ":" ":"

-- do not parse --, ->, or -|
pMinus :: CharParser st String
pMinus = pSymC "-" "->|"

pSymS :: String -> CharParser st String
pSymS s = tryString s << skip

pSym :: String -> CharParser st ()
pSym = forget . pSymS

pComma :: CharParser st ()
pComma = pSym ","

pEqual :: CharParser st ()
pEqual = pSym "="

pGenParens :: String -> String -> CharParser st a -> CharParser st a
pGenParens o c p =
  pSym o >> p << pSym c

pParens :: CharParser st a -> CharParser st a
pParens = pGenParens "(" ")"

pSqBrackets :: CharParser st a -> CharParser st a
pSqBrackets = pGenParens "[" "]"

pConid :: CharParser st String
pConid = reserved keywordstxt (upper <:> many pChar) << skip

pVarid :: CharParser st String
pVarid = reserved casl_structured_reserved_words (lower <:> many pChar) << skip

pString :: CharParser st String
pString = (stringLit <|> sQuoted) << skip

pADLid :: CharParser st Token
pADLid = parseToken $ pConid <|> pVarid <|> pString

-- | parse contexts but do not require CONTEXT blocks
pArchitecture :: CharParser st Context
pArchitecture = fmap Context $ flat $ many1
  $ pContext <|> flat (many1 pContextElement)

pContext :: CharParser st [PatElem]
pContext = do
  pKey "CONTEXT"
  pConid
  option () $ do
    pColon
    pExpr
    forget $ optionL $ do
      pKey "BINDING"
      sepBy1 pBind pComma
  optionL $ do
    pKey "EXTENDS"
    sepBy1 pConid pComma
  ps <- many pContextElement
  pKey "ENDCONTEXT"
  return $ concat ps

pBind :: CharParser st String
pBind = pKey "BIND" >> pDeclaration << pKey "TOPHP" >> (pConid <|> pString)

-- | parse a context element but do not require the PATTERN block
pContextElement :: CharParser st [PatElem]
pContextElement = pPattern <|> flat (many1 pPatElem)
  <|> single (pObjDef <|> pPopulation)
  <|> pSqlplug <|> pPhpplug

pPopulation :: CharParser st PatElem
pPopulation = do
  pKey "POPULATION"
  r <- pMorphism
  pKey "CONTAINS"
  pContent False r

pPattern :: CharParser st [PatElem]
pPattern = pKey "PATTERN" >> (pConid <|> pString)
           >> flat (many pPatElem)
           << pKey "ENDPATTERN"

pPatElem :: CharParser st [PatElem]
pPatElem = pDeclaration <|> pConceptDef <|> pExplain
  <|> single (pRuleDef <|> pGen <|> pKeyDef)

pDeclaration :: CharParser st [PatElem]
pDeclaration = do
  n <- try $ parseToken pVarid << pSym "::"
  c1 <- pConcept
  s <- parseToken $ pSymS "*" <|> pSymS "->"
  let ps = if tokStr s == "->" then
        map (flip RangedProp $ tokPos s) [Uni, Tot] else []
  c2 <- pConcept
  as <- optionL pProps
  optionL pPragma
  optionL $ do
    pKey "EXPLANATION"
    pString
  let r = Sgn n c1 c2
  p <- optionL $ do
    pEqual
    single $ pContent True r
  pSym "."
  return $ Pm (ps ++ as) r (not $ null p) : p

pRangedProp :: Prop -> CharParser st RangedProp
pRangedProp p = liftM2 (flip RangedProp)
    (liftM tokPos $ parseToken $ pKeyS $ showProp p) $ return p

pProps :: CharParser st [RangedProp]
pProps = pSqBrackets $ sepBy
  (choice $ map pRangedProp allProps) pComma

pPragma :: CharParser st [String]
pPragma = pKey "PRAGMA" >> many1 pString

pConceptDef :: CharParser st [PatElem]
pConceptDef = do
  pKey "CONCEPT"
  pConcept
  pString
  optionL pString
  return []

pKeyDef :: CharParser st PatElem
pKeyDef = do
  pKey "KEY"
  t <- pLabelProps
  c <- pConcept
  l <- pParens $ sepBy1 pKeyAtt pComma
  return $ Pk $ KeyDef t c l

pLabelProps :: CharParser st Token
pLabelProps = do
  n <- pADLid
  optionL $ pGenParens "{" "}" $ sepBy1 pADLid pComma
  pColon
  return n

pKeyAtt :: CharParser st KeyAtt
pKeyAtt = liftM2 KeyAtt (optionMaybe $ try pLabelProps) pExpr

pObjDef :: CharParser st PatElem
pObjDef = pKey "SERVICE" >> fmap Service pObj

pObj :: CharParser st Object
pObj = do
  n <- pLabelProps
  e <- pExpr
  as <- optionL (pKey "ALWAYS" >> many pProp')
  os <- optionL (pEqual >> pSqBrackets (sepBy pObj pComma))
  return $ Object n e as os

pProp' :: CharParser st RangedProp
pProp' = choice $ map pRangedProp [Uni, Tot, Prop]

pSqlplug :: CharParser st [PatElem]
pSqlplug = pKey "SQLPLUG" >> pObj >> return []

pPhpplug :: CharParser st [PatElem]
pPhpplug = pKey "PHPPLUG" >> pObj >> return []

pExplain :: CharParser st [PatElem]
pExplain = do
  pKey "EXPLAIN"
  choice $ map pKey
    [ "CONCEPT", "RELATION", "RULE", "KEY", "SERVICE", "PATTERN"
    , "POPULATION", "SQLPLUG", "PHPPLUG" ]
  pADLid
  pLanguageID
  pRefID
  pExpl
  return []

pLanguageID :: CharParser st String
pLanguageID = pKey "IN" >> (pKeyS "DUTCH" <|> pKeyS "ENGLISH")

pRefID :: CharParser st String
pRefID = optionL $ pKey "REF" >> pString

pExpl :: CharParser st String
pExpl = nestedComment "{+" "-}"

pContent :: Bool -> Relation -> CharParser st PatElem
pContent b r = fmap (Population b r) $ pSqBrackets $ sepBy pRecord $ pSym ";"

pRecord :: CharParser st Pair
pRecord = let ps = parseToken pString in
  pParens $ liftM2 Pair ps $ pComma >> ps

pRuleDef :: CharParser st PatElem
pRuleDef = do
  h <- option Always pSignalOrAlways
  e1 <- pExpr
  r <- option (Truth e1) $ do
    sym <- choice $ map pSymS ["=", "|-", "-|"]
    e2 <- pExpr
    return $ Rule e1 (case sym of
      "=" -> Equivalence
      "|-" -> Implication
      "-|" -> ReverseImpl
      _ -> error "pRuleDef") e2
  option "" $ do
    pKey "EXPLANATION"
    pString
  return $ Pr h r

pSignalOrAlways :: CharParser st RuleHeader
pSignalOrAlways =
  fmap (RuleHeader SignalOn) (pKey "SIGNAL" >> pADLid << pKey "ON")
  <|> (pKey "RULE" >> liftM2 (flip RuleHeader) pADLid
         (choice $ map (\ r -> pKey (showRuleKind r) >> return r)
         [Maintains, Signals]))

pGen :: CharParser st PatElem
pGen = do
  pKey "GEN"
  c1 <- pConcept
  pKey "ISA"
  c2 <- pConcept
  return $ Pg c1 c2

pTwo :: CharParser st (Concept, Concept)
pTwo = option (Anything, Anything)
  $ pSqBrackets $ do
  c1 <- pConcept
  c2 <- option c1 $ do
    pSym "*"
    pConcept
  return (c1, c2)

pConcept :: CharParser st Concept
pConcept = fmap C . parseToken $ pConid <|> pString <|> pKeyS "ONE"

pMorphism :: CharParser st Relation
pMorphism = do
  nm <- parseToken $ pKeyS "I" <|> pKeyS "V" <|> pVarid <|> (sQuoted << skip)
  (c1, c2) <- pTwo
  return $ Sgn nm c1 c2

pExpr :: CharParser st Expression
pExpr = pPrec Fu pFactorI "\\/"

pFactorI :: CharParser st Expression
pFactorI = pPrec Fi pFactor "/\\"

pFactor :: CharParser st Expression
pFactor = pPrec Fd pTermD "!"

pTermD :: CharParser st Expression
pTermD = pPrec Fc pTerm ";"

pPrec :: MulOp -> CharParser st Expression -> String
  -> CharParser st Expression
pPrec f p s = do
  es <- sepBy1 p $ pSym s
  return $ case es of
    [e] -> e
    _ -> MulExp f es

pTerm :: CharParser st Expression
pTerm = do
  ms <- many pMinus
  e <- pParens pExpr <|> fmap Tm pMorphism
  rs <- many $ choice $ map (pSymS . (: [])) "+*~"
  let p = foldl (\ r c -> UnExp (case c of
        "+" -> K1
        "*" -> K0
        "~" -> Co
        _ -> error "pTerm post strings") r) e rs
  return $ foldl (\ r _ -> UnExp Cp r) p ms
