{- |
Module      :  $Header$
Description :  parsing SparQ CompositionTables
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  fmossa@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parses CompositionTables in SparQ(Lisp)-Format using Parsec
 <http://www.cs.uu.nl/~daan/parsec.html>
-}

module CASL.CompositionTable.ParseSparQ (parseSparQTableFromFile) where

import Text.ParserCombinators.Parsec
import CASL.CompositionTable.CompositionTable
import Common.Lexer
import Common.Parsec

parseSparQTableFromFile :: String -> IO (Either ParseError Table)
parseSparQTableFromFile = parseFromFile parseSparQTable

parseSparQTable :: Parser Table
parseSparQTable = do
  skipMany skippable
  calculusName <- parseCalculusName
  skipMany skippable
  identityRelation <- parseCalculusProperties
  skipMany skippable
  ct <- parseConversetable
  try (do
      skipMany skippable
      parseReflectionOperations
      skipMany skippable)
    <|> skipMany skippable
  br <- parseBaseRelations
  skipMany skippable
  compt <- parseCompTable
  return $ Table
    (Table_Attrs calculusName (Baserel identityRelation) br)
    compt ct (Reflectiontable []) (Models [])

parseArBaPa :: Parser String
parseArBaPa = try parseArity <|> try parseBasisEntity <|> try parseQualifier

parseCalculusProperties :: Parser String
parseCalculusProperties = do
  many (parseArBaPa <|> try parseParametric)
  ide <- parseIdentityRelation
  many parseArBaPa
  many skippable
  return ide

parseParametric :: Parser String
parseParametric = do
  many skippable
  string ":parametric?"
  many space
  word

parseArity :: Parser String
parseArity = do
  many skippable
  string ":arity"
  many space
  string ":"
  word

parseBasisEntity :: Parser String
parseBasisEntity = do
  many skippable
  string ":basis-entity"
  many space
  string ":"
  word

parseIdentityRelation :: Parser String
parseIdentityRelation = do
  many skippable
  string ":identity-relation"
  many space
  ide <- parseRelationId
  return (baserelBaserel ide)

parseQualifier :: Parser String
parseQualifier = do
  many skippable
  string ":qualifier"
  many space
  parseQualifierBrace

parseQualifierBrace :: Parser String
parseQualifierBrace = do
  string "(" <|> string "#'("
  many (many1 (noneOf "()") <|> try parseQualifierBrace)
  string ")"
  return ""

skippable :: Parser String
skippable = many1 space <|> parseAnnotation

parseAnnotation :: Parser String
parseAnnotation = try (do
     string ";;#|"
     many (many1 (noneOf ";") <|>
           try (string ";" << notFollowedBy (char ';')))
     string ";;|#")
   <|> do
     many space
     string ";"
     many (string ";")
     many (noneOf "\n")
     string "\n"

parseCalculusName :: Parser String
parseCalculusName = do
  many skippable
  string "(def-calculus"
  many space
  s <- parseQuotedStrings
  space
  return s

parseQuotedStrings :: Parser String
parseQuotedStrings = do
  char '"'
  cs <- many1 (noneOf "\"")
  char '"'
  return cs

word :: Parser String
word = many1 (letter <|> char '_' <|> char '.' <|> char '-' <|> digit)

parseBaseRelations :: Parser [Baserel]
parseBaseRelations = do
  many skippable
  string ":base-relations"
  many skippable
  oParenT
  baserels <- many1 parseRelationId
  cParenT
  return baserels

parseCompTable :: Parser Compositiontable
parseCompTable = do
  many skippable
  string ":composition-operation"
  many skippable
  oParenT
  cmptabentries <- parseComptabentryList
  cParenT
  return (Compositiontable cmptabentries)

parseComptabentryList :: Parser [Cmptabentry]
parseComptabentryList = many1 parseComptabentry

parseComptabentry :: Parser Cmptabentry
parseComptabentry = do
  many skippable
  oParenT
  rel1 <- parseRelationId
  rel2 <- parseRelationId
  results <- parseComptabentryResults
  cParenT
  return (Cmptabentry (Cmptabentry_Attrs rel1 rel2) results)

parseComptabentryResults :: Parser [Baserel]
parseComptabentryResults = try (do
    oParenT
    results <- many1 parseRelationId
    cParenT
    return results)
  <|> (tryString "NIL" >> return [])
  <|> do
    result <- parseRelationId
    return [result]
  <|> do
    oParenT
    many space
    cParenT
    return []

parseConversetable :: Parser Conversetable
parseConversetable = try (do
    entry1 <- parseInverse
    entry3 <- parseShortcut
    entry2 <- parseHoming
    return (Conversetable_Ternary entry1 entry3 entry2))
  <|> do
    entry <- parseConverse
    return (Conversetable entry)

parseConverse :: Parser [Contabentry]
parseConverse = do
  many skippable
  string ":converse-operation"
  many skippable
  oParenT
  invrels <- many1 parseContabentry
  cParenT
  return invrels

parseContabentry:: Parser Contabentry
parseContabentry = do
  many skippable
  oParenT
  id1 <- parseRelationId
  id2 <- parseRelationId
  cParenT
  return (Contabentry id1 id2)

parseContabentryList :: String -> Parser [Contabentry_Ternary]
parseContabentryList s = do
  many skippable
  string s
  many skippable
  oParenT
  invrels <- many1 parseContabentryTernary
  cParenT
  return invrels

parseContabentryTernary :: Parser Contabentry_Ternary
parseContabentryTernary = do
  many skippable
  oParenT
  id1 <- parseRelationId
  ids <- many1 parseRelationId <|> parseBracedRelationIds
  cParenT
  return (Contabentry_Ternary id1 ids)

parseBracedRelationIds :: Parser [Baserel]
parseBracedRelationIds = do
  many skippable
  oParenT
  ids <- many1 parseRelationId
  cParenT
  return ids

parseReflectionOperations :: Parser String
parseReflectionOperations =  do
  many skippable
  string ":reflection-operation"
  many skippable
  oParenT
  many1 parseContabentry
  cParenT
  return ""

parseInverse :: Parser [Contabentry_Ternary]
parseInverse = parseContabentryList ":inverse-operation"

parseHoming :: Parser [Contabentry_Ternary]
parseHoming = parseContabentryList ":homing-operation"

parseShortcut :: Parser [Contabentry_Ternary]
parseShortcut = parseContabentryList ":shortcut-operation"

parseRelationId :: Parser Baserel
parseRelationId = do
  chars <- many1 (noneOf "() \r\v\f\t\160\n")
  skip
  return (Baserel chars)
