{- |
Module      :  $Header$
Description :  ADL syntax parser
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

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
keywordstxt = map showUp allProps ++
  [ "CONTEXT", "ENDCONTEXT", "EXTENDS"
  , "PATTERN", "ENDPATTERN"
  , "SERVICE", "INITIAL", "SQLPLUG", "PHPPLUG"
  , "POPULATION", "CONTAINS"
  , "PROP", "ALWAYS"
  , "RULE", "MAINTAINS", "SIGNALS", "SIGNAL", "ON"
  , "RELATION", "CONCEPT", "KEY"
  , "IMPORT", "GEN", "ISA", "I", "V", "S"
  , "PRAGMA", "EXPLANATION", "EXPLAIN", "IN", "REF", "ENGLISH", "DUTCH"
  , "ONE", "BIND", "TOPHP", "BINDING", "BYPLUG"
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

-- | with true argument exclude CASL keywords
pVarid :: Bool -> CharParser st String
pVarid b = (if b then reserved criticalKeywords else id)
  $ ((lower <|> char '_') <:> many pChar) << skip

pString :: CharParser st String
pString = (stringLit <|> sQuoted) << skip

pADLid :: CharParser st Token
pADLid = parseToken $ pConid <|> pVarid False <|> pString

-- | parse contexts but do not require CONTEXT blocks
pArchitecture :: CharParser st Context
pArchitecture = pContext
  <|> fmap (mkContext Nothing) (flat $ many1 $ pContextElement True)

pContext :: CharParser st Context
pContext = do
  pKey "CONTEXT"
  c <- parseToken pConid
  option () $ do
    pColon
    pRule False
    forget $ optionL $ do
      pKey "BINDING"
      sepBy1 pBind pComma
  optionL $ do
    pKey "EXTENDS"
    sepBy1 pConid pComma
  ps <- many $ pContextElement False
  pKey "ENDCONTEXT"
  return $ mkContext (Just c) $ concat ps

pBind :: CharParser st String
pBind = pKey "BIND" >> pDeclaration False << pKey "TOPHP"
  >> (pConid <|> pString)

-- | parse a context element but do not require the PATTERN block
pContextElement :: Bool -> CharParser st [PatElem]
pContextElement b = pPattern <|> flat (many1 $ pPatElem b)
  <|> single (pObjDef <|> pPopulation)

pPopulation :: CharParser st PatElem
pPopulation = do
  pKey "POPULATION"
  r <- pMorphism False
  pKey "CONTAINS"
  pContent False r

pPattern :: CharParser st [PatElem]
pPattern = pKey "PATTERN" >> (pConid <|> pString)
           >> flat (many $ pPatElem False)
           << pKey "ENDPATTERN"

pPatElem :: Bool -> CharParser st [PatElem]
pPatElem b = pDeclaration b <|> pConceptDef <|> pExplain
  <|> single (pRuleDef b <|> pGen <|> pKeyDef)

pDeclaration :: Bool -> CharParser st [PatElem]
pDeclaration b = do
  n <- try $ parseToken (pVarid b) << pSym "::"
  c1 <- pConcept
  s <- parseToken $ pSymS "*" <|> pSymS "->"
  let ps = if tokStr s == "->" then
        map (flip RangedProp $ tokPos s) [Uni, Tot] else []
  c2 <- pConcept
  pByplug
  as <- optionL pProps
  pByplug
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

pByplug :: CharParser st Bool
pByplug = option False $ pKey "BYPLUG" >> return True

pConceptDef :: CharParser st [PatElem]
pConceptDef = do
  pKey "CONCEPT"
  pConcept
  pByplug
  pString
  optionL pString
  return []

pKeyDef :: CharParser st PatElem
pKeyDef = do
  pKey "KEY"
  t <- pLabelProps
  c <- pConcept <|> (pKey "I" >> pSqBrackets pConcept)
  let ks = sepBy1 pKeyAtt pComma
  l <- pParens ks <|> pSqBrackets ks
  return $ Pk $ KeyDef t c l

pLabelProps :: CharParser st Token
pLabelProps = do
  n <- pADLid
  optionL $ pGenParens "{" "}" $ sepBy1 pADLid pComma
  option "" pColon
  return n

pKeyAtt :: CharParser st KeyAtt
pKeyAtt = liftM2 KeyAtt (optionMaybe $ try pLabelProps) $ pRule False

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
  e <- pRule False <|> fmap (Tm . Sgn (mkSimpleId "I")) pTwo
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

pRuleDef :: Bool -> CharParser st PatElem
pRuleDef b = do
  h <- option Always pSignalOrAlways
  r <- pRule $ b && h == Always
  option () $ do
    pKey "COMPUTING"
    pMorphism False
    return ()
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

pMorphism :: Bool -> CharParser st Relation
pMorphism b = do
  nm <- parseToken $ choiceP pKey bRels <|> pVarid b <|> (sQuoted << skip)
  ty <- pTwo
  return $ Sgn nm ty

pRule :: Bool -> CharParser st Rule
pRule = pPrec Re . pImpl

pImpl :: Bool -> CharParser st Rule
pImpl b = do
  e <- pExpr b
  option e $ do
    o <- choiceS pSym [Ri, Rr]
    es <- sepBy1 (pExpr False) $ pSym (show o)
    return $ MulExp o $ e : es

pExpr :: Bool -> CharParser st Rule
pExpr = pPrec Fu . pFactorI

pFactorI :: Bool -> CharParser st Rule
pFactorI = pPrec Fi . pFactor

pFactor :: Bool -> CharParser st Rule
pFactor = pPrec Fd . pTermD

pTermD :: Bool -> CharParser st Rule
pTermD = pPrec Fc . pTerm

pPrec :: MulOp -> CharParser st Rule -> CharParser st Rule
pPrec f p = do
  es <- sepBy1 p $ try $ pSym (show f) >> notFollowedBy (char '[')
                   -- to avoid conflict in objects
  return $ case es of
    [e] -> e
    _ -> MulExp f es

pTerm :: Bool -> CharParser st Rule
pTerm b = do
  ms <- many pMinus
  e <- pParens (pRule False) <|> fmap Tm (pMorphism b)
  rs <- many $ choiceS pSym [K0, K1, Co]
  let p = foldl (flip UnExp) e rs
  return $ foldl (\ r _ -> UnExp Cp r) p ms
