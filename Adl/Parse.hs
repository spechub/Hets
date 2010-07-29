{- |
Module      :  $Header$
Description :  ADL syntax parser
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Main where

import Common.Parsec
import Common.DocUtils
import Common.Doc hiding (space)
import System.Environment
import Text.ParserCombinators.Parsec
import Haskell.Wrapper

import Adl.As
import Adl.Print ()

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

skip :: CharParser st ()
skip = skipMany $ forget space <|> forget (nestComment <|> lineComment)

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
pVarid = (lower <:> many pChar) << skip

pString :: CharParser st String
pString = (stringLit <|> charLit) << skip

pADLid :: CharParser st String
pADLid = pConid <|> pVarid <|> pString

pArchitecture :: CharParser st [PatElem]
pArchitecture = flat $ many1 pContext

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

pContextElement :: CharParser st [PatElem]
pContextElement = pPattern
  <|> fmap (: [])
      (choice [pObjDef, pDeclaration, pConceptDef, pKeyDef, pExplain])
  <|> fmap (const []) (pSqlplug <|> pPhpplug
  <|> (pKey "POPULATION" >> pMorphism << pKey "CONTAINS" >> pContent))

pPattern :: CharParser st [PatElem]
pPattern = pKey "PATTERN" >> (pConid <|> pString)
           >> many pPatElem
           << pKey "ENDPATTERN"

pPatElem :: CharParser st PatElem
pPatElem = pDeclaration <|> fmap Pr pRuleDef
  <|> pGen <|> fmap (const Ignored)
          (pConceptDef <|> pKeyDef <|> pExplain)

pDeclaration :: CharParser st PatElem
pDeclaration = do
  n <- try $ pVarid << pSym "::"
  c1 <- pConcept
  s <- pSymS "*" <|> pSymS "->"
  let ps = if s == "->" then [Uni, Tot] else []
  c2 <- pConcept
  as <- optionL pProps
  optionL pPragma
  optionL $ do
    pKey "EXPLANATION"
    pString
  option () $ do
    pEqual
    pContent
    return ()
  pSym "."
  return $ Pm (ps ++ as) $ Sgn n c1 c2

pProps :: CharParser st [Prop]
pProps = pSqBrackets $
  sepBy (choice $ map (\ p -> pKey (showProp p) >> return p) allProps) pComma

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
  pParens $ sepBy1 pKeyAtt pComma
  return Ignored

pLabelProps :: CharParser st String
pLabelProps = do
  n <- pADLid
  optionL $ pGenParens "{" "}" $ sepBy1 pADLid pComma
  pColon
  return n

pKeyAtt :: CharParser st Expression
pKeyAtt = do
 optionMaybe $ try pLabelProps
 pExpr

pObjDef :: CharParser st PatElem
pObjDef = pKey "SERVICE" >> fmap Service pObj

pObj :: CharParser st Object
pObj = do
  n <- pLabelProps
  e <- pExpr
  as <- optionL (pKey "ALWAYS" >> many pProp')
  os <- optionL (pEqual >> pSqBrackets (sepBy pObj pComma))
  return $ Object n e as os

pProp' :: CharParser st Prop
pProp' = choice $ map (\ p -> pKey (showProp p) >> return p) [Uni, Tot, Prop]

pSqlplug :: CharParser st PatElem
pSqlplug = pKey "SQLPLUG" >> pObj >> return Ignored

pPhpplug :: CharParser st PatElem
pPhpplug = pKey "PHPPLUG" >> pObj >> return Ignored

pExplain :: CharParser st PatElem
pExplain = do
  pKey "EXPLAIN"
  choice $ map pKey
    [ "CONCEPT", "RELATION", "RULE", "KEY", "SERVICE", "PATTERN"
    , "POPULATION", "SQLPLUG", "PHPPLUG" ]
  pADLid
  pLanguageID
  pRefID
  pExpl
  return Ignored

pLanguageID :: CharParser st String
pLanguageID = pKey "IN" >> (pKeyS "DUTCH" <|> pKeyS "ENGLISH")

pRefID :: CharParser st String
pRefID = optionL $ pKey "REF" >> pString

pExpl :: CharParser st String
pExpl = nestedComment "{+" "-}"

pContent :: CharParser st PatElem
pContent = pSqBrackets (sepBy pRecord $ pSym ";") >> return Ignored

pRecord :: CharParser st (String, String)
pRecord = pParens $ pair pString $ pComma >> pString

pRuleDef :: CharParser st Rule
pRuleDef = do
  option "" pSignalOrAlways
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
pTwo = option (Anything, Anything)
  $ pSqBrackets $ do
  c1 <- pConcept
  c2 <- option c1 $ do
    pSym "*"
    pConcept
  return (c1, c2)

pConcept :: CharParser st Concept
pConcept = fmap C $ pConid <|> pString <|> pKeyS "ONE"

pMorphism :: CharParser st Expression
pMorphism = do
  nm <- pKeyS "I" <|> pKeyS "V" <|> pVarid <|> (charLit << skip)
  (c1, c2) <- pTwo
  return $ Tm $ Sgn nm c1 c2

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
  ms <- many $ pMinus
  e <- pParens pExpr <|> pMorphism
  rs <- many $ choice $ map (pSymS . (: [])) "+*~"
  let p = foldl (\ r c -> UnExp (case c of
        "+" -> K1
        "*" -> K0
        "~" -> Co
        _ -> error "pTerm post strings") r) e rs
  return $ foldl (\ r _ -> UnExp Cp r) p ms

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process f = do
  s <- readFile f
  case parse (skip >> pArchitecture << eof) f s of
             Right es -> print $ vcat $ map pretty es
             Left err -> fail $ show err
