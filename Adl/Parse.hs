{- |
Module      :  $Header$
Description :  ADL syntax parser
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.Parse where

import Adl.As

import Common.Id
import Common.Lexer (parseToken)
import Common.Parsec
import Common.Token (criticalKeywords)
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
pVarid = reserved criticalKeywords
  ((lower <|> char '_') <:> many pChar) << skip

pString :: CharParser st String
pString = (stringLit <|> sQuoted) << skip

pADLid :: CharParser st Token
pADLid = parseToken $ pConid <|> pVarid <|> pString

-- | parse contexts but do not require CONTEXT blocks
pArchitecture :: CharParser st Context
pArchitecture = pContext
  <|> fmap (Context Nothing) (flat $ many1 pContextElement)

pContext :: CharParser st Context
pContext = do
  pKey "CONTEXT"
  c <- parseToken pConid
  option () $ do
    pColon
    pRule
    forget $ optionL $ do
      pKey "BINDING"
      sepBy1 pBind pComma
  optionL $ do
    pKey "EXTENDS"
    sepBy1 pConid pComma
  ps <- many pContextElement
  pKey "ENDCONTEXT"
  return $ Context (Just c) $ concat ps

pBind :: CharParser st String
pBind = pKey "BIND" >> pDeclaration << pKey "TOPHP" >> (pConid <|> pString)

-- | parse a context element but do not require the PATTERN block
pContextElement :: CharParser st [PatElem]
pContextElement = pPattern <|> flat (many1 pPatElem)
  <|> single (pObjDef <|> pPopulation)

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
  let r = Sgn n $ RelType c1 c2
  p <- optionL $ do
    pEqual
    single $ pContent True r
  option () $ pSym "."
  return $ Pm (ps ++ as) r (not $ null p) : p

pRangedProp :: Prop -> CharParser st RangedProp
pRangedProp p = liftM2 (flip RangedProp)
    (liftM tokPos $ parseToken $ pKeyS $ showUp p) $ return p

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
pKeyAtt = liftM2 KeyAtt (optionMaybe $ try pLabelProps) pRule

choiceP :: (a -> CharParser st ()) -> [a] -> CharParser st a
choiceP p = choice . map (\ a -> p a >> return a)

choiceS :: Show a => (String -> CharParser st ()) -> [a] -> CharParser st a
choiceS p = choiceP $ p . show

pObjDef :: CharParser st PatElem
pObjDef = liftM2 Plug (choiceP (pKey . showUp)
   [Service, Sqlplug, Phpplug]) pObj

pObj :: CharParser st Object
pObj = do
  n <- pLabelProps
  e <- pRule
  as <- optionL (pKey "ALWAYS" >> many pProp')
  os <- optionL (pEqual >> pSqBrackets (sepBy pObj pComma))
  return $ Object n e as os

pProp' :: CharParser st RangedProp
pProp' = choice $ map pRangedProp [Uni, Tot, Prop]

pExplain :: CharParser st [PatElem]
pExplain = do
  pKey "EXPLAIN"
  choiceP pKey
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
  r <- pRule
  option "" $ do
    pKey "EXPLANATION"
    pString
  return $ Pr h r

pSignalOrAlways :: CharParser st RuleHeader
pSignalOrAlways =
  fmap (RuleHeader SignalOn) (pKey "SIGNAL" >> pADLid << pKey "ON")
  <|> (pKey "RULE" >> liftM2 (flip RuleHeader) pADLid
         (choiceP (pKey . showRuleKind) [Maintains, Signals]))

pGen :: CharParser st PatElem
pGen = do
  pKey "GEN"
  c1 <- pConcept
  pKey "ISA"
  c2 <- pConcept
  return $ Pg c1 c2

pTwo :: CharParser st RelType
pTwo = option (RelType Anything Anything)
  $ pSqBrackets $ do
  c1 <- pConcept
  c2 <- option c1 $ do
    pSym "*"
    pConcept
  return $ RelType c1 c2

pConcept :: CharParser st Concept
pConcept = fmap C . parseToken $ pConid <|> pString <|> pKeyS "ONE"

pMorphism :: CharParser st Relation
pMorphism = do
  nm <- parseToken $ choiceP pKey bRels <|> pVarid <|> (sQuoted << skip)
  ty <- pTwo
  return $ Sgn nm ty

pRule :: CharParser st Rule
pRule = pPrec Re pImpl

pImpl :: CharParser st Rule
pImpl = do
  e <- pExpr
  option e $ do
    o <- choiceS pSym [Ri, Rr]
    es <- sepBy1 pExpr $ pSym (show o)
    return $ MulExp o $ e : es

pExpr :: CharParser st Rule
pExpr = pPrec Fu pFactorI

pFactorI :: CharParser st Rule
pFactorI = pPrec Fi pFactor

pFactor :: CharParser st Rule
pFactor = pPrec Fd pTermD

pTermD :: CharParser st Rule
pTermD = pPrec Fc pTerm

pPrec :: MulOp -> CharParser st Rule -> CharParser st Rule
pPrec f p = do
  es <- sepBy1 p $ try $ pSym (show f) >> notFollowedBy (char '[')
                   -- to aovid conflict in objects
  return $ case es of
    [e] -> e
    _ -> MulExp f es

pTerm :: CharParser st Rule
pTerm = do
  ms <- many pMinus
  e <- pParens pRule <|> fmap Tm pMorphism
  rs <- many $ choiceS pSym [K0, K1, Co]
  let p = foldl (flip UnExp) e rs
  return $ foldl (\ r _ -> UnExp Cp r) p ms
