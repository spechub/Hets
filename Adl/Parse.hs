{- |
Module      :  $Header$
Description :  ADL syntax parser
Copyright   :  (c) Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.Parse where

import Common.Parsec
import Text.ParserCombinators.Parsec
import Haskell.Wrapper

import Adl.As

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

keywordsops :: [String]
keywordsops =
  [ "-|", "|-", "-", "->", ">", "=", "~", "+", ";", "!", "*", "::", ":"
  , "\\/", "/\\", "\\", "/", "<>" ]

specialchars :: String
specialchars = "()[].,{}"

skip :: CharParser st ()
skip = skipMany $ spaces <|> forget (nestComment <|> lineComment)

pKey :: String -> CharParser st ()
pKey = forget . pKeyS

pKeyS :: String -> CharParser st String
pKeyS s = try (string s << notFollowedBy letter) << skip

pSym :: String -> CharParser st ()
pSym = forget . pSymS

pSymS :: String -> CharParser st String
pSymS s = tryString s << skip

pConid :: CharParser st String
pConid = reserved keywordstxt (upper <:> many letter) << skip

pVarid :: CharParser st String
pVarid = (lower <:> many letter) << skip

pString :: CharParser st String
pString = stringLit <|> charLit

pADLid :: CharParser st String
pADLid = pConid <|> pVarid <|> pString

pArchitecture :: CharParser st [PatElem]
pArchitecture = flat $ many1 pContext

pContext :: CharParser st [PatElem]
pContext = do
  pKey "CONTEXT"
  pConid
  option () $ do
    pSym ":"
    pExpr
    forget $ optionL $ do
      pKey "BINDING"
      sepBy1 pBind $ pSym ","
  optionL $ do
    pKey "EXTENDS"
    sepBy1 pConid $ pSym ","
  ps <- many pContextElement
  pKey "ENDCONTEXT"
  return $ concat ps

pBind :: CharParser st String
pBind = pKey "BIND" >> pDeclaration << pKey "TOPHP" >> (pConid <|> pString)

pContextElement :: CharParser st [PatElem]
pContextElement = pPattern <|> fmap (const [])
  (pDeclaration <|> pConceptDef <|> pKeyDef
  <|> pObjDef <|> pSqlplug <|> pPhpplug <|> pExplain
  <|> (pKey "POPULATION" >> pMorphism << pKey "CONTAINS" >> pContent))

pPattern :: CharParser st [PatElem]
pPattern = pKey "PATTERN" >> (pConid <|> pString)
           >> many pPatElem
           <<  pKey "ENDPATTERN"

pPatElem :: CharParser st PatElem
pPatElem = fmap Pr pRuleDef
  <|> pGen <|> pDeclaration <|> fmap (const Ignored)
          (pConceptDef <|> pKeyDef <|> pExplain)

pDeclaration :: CharParser st PatElem
pDeclaration = do
  n <- pVarid
  pSym "::"
  c1 <- pConcept
  s <- pSymS "*" <|> pSymS "->"
  let ps = if s == "->" then [Uni, Tot] else []
  c2 <- pConcept
  as <- optionL pProps
  optionL pPragma
  optionL $ do
    pKey "EXPLANATION"
    pString
  optionL $ do
    pSym "="
    pContent
  pSym "."
  return $ Pm (ps ++ as) $ Sgn n c1 c2

pProps :: CharParser st [Prop]
pProps = do
 pSym "["
 ps <- sepBy1 (choice $ map (\ p -> pKey (showProp p) >> return p) allProps)
   $ pSym ","
 pSym "]"
 return ps

pPragma :: CharParser st [String]
pPragma = pKey "PRAGMA" >> many1 pString

pConceptDef :: CharParser st PatElem
pConceptDef = do
  pKey "CONCEPT"
  pConcept
  pString
  optionL pString
  return Ignored

pKeyDef :: CharParser st PatElem
pKeyDef = do
  pKey "KEY"
  pLabelProps
  pConcept
  pSym "("
  sepBy1 pKeyAtt $ pSym ","
  pSym ")"
  return Ignored

pLabelProps :: CharParser st ()
pLabelProps = do
  pADLid
  optionL $ do
    pSym "{"
    ns <- sepBy1 pADLid $ pSym ","
    pSym "}"
    return ns
  pKey ":"

pKeyAtt :: CharParser st Expression
pKeyAtt = do
 option () $ try pLabelProps
 pExpr

pObjDef = undefined
pSqlplug = undefined
pPhpplug = undefined
pExplain = undefined
pContent = undefined

pRuleDef :: CharParser st Rule
pRuleDef = do
  option "" pSignalOrAlways
  e1 <- pExpr
  r <- option (Truth e1) $ do
    sym <- choice $ map pSymS ["=", "|-", "-|"]
    e2 <- pExpr
    return $ case sym of
      "=" -> Rule e1 Equivalence e2
      "|-" -> Rule e1 Implication e2
      "-|" -> Rule e2 Implication e1
      _ -> error "pRuleDef"
  option "" $ do
    pKey "EXPLANATION"
    pString
  return r

pSignalOrAlways :: CharParser st String
pSignalOrAlways =
  (pKey "SIGNAL" >> pADLid << pKey "ON")
  <|> (pKey "RULE" >> pADLid << (pKey "MAINTAINS" <|> pKey "SIGNALS"))

pGen :: CharParser st PatElem
pGen = do
  pKey "GEN"
  c1 <- pConcept
  pKey "ISA"
  c2 <- pConcept
  return $ Pg c1 c2

pTwo :: CharParser st (Concept, Concept)
pTwo = option (Anything, Anything) $ do
  pSym "["
  c1 <- pConcept
  c2 <- option c1 $ do
    pKey "*"
    pConcept
  pSym "]"
  return (c1, c2)

pConcept :: CharParser st Concept
pConcept = fmap C $ pConid <|> pString <|> pKeyS "ONE"

pMorphism :: CharParser st Expression
pMorphism = do
  nm <- pKeyS "I" <|> pKeyS "V" <|> pVarid <|> charLit
  (c1, c2) <- pTwo
  return $ Tm $ Sgn nm c1 c2

pExpr :: CharParser st Expression
pExpr = do
  es <- sepBy1 pFactorI $ pSym "\\/"
  return $ case es of
    [e] -> e
    _ -> MulExp Fu es

pFactorI :: CharParser st Expression
pFactorI = do
  es <- sepBy1 pFactor $ pSym "/\\"
  return $ case es of
    [e] -> e
    _ -> MulExp Fi es

pFactor :: CharParser st Expression
pFactor = do
  es <- sepBy1 pTermD $ pSym "!"
  return $ case es of
    [e] -> e
    _ -> MulExp Fd es

pTermD :: CharParser st Expression
pTermD = do
  es <- sepBy1 pTerm $ pSym ";"
  return $ case es of
    [e] -> e
    _ -> MulExp Fc es

pTerm :: CharParser st Expression
pTerm = do
  ms <- many $ char '-'
  e <- (pSym "(" >> pExpr << pSym ")") <|> pMorphism
  rs <- many $ choice $ map char "+*~"
  let p = foldl (\ r c -> case c of
        '+' -> UnExp K1 r
        '*' -> UnExp K0 r
        '~' -> UnExp Co r
        _ -> error "pTerm post strings") e rs
  return $ foldl (\ r _ -> UnExp Cp r) p ms
