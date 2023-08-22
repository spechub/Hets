{- |
Module      :  ./CASL/CompositionTable/ParseSparQ.hs
Description :  parsing SparQ CompositionTables
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  fmossa@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parses CompositionTables in SparQ(Lisp)-Format using Parsec
 <http://www.cs.uu.nl/~daan/parsec.html>
-}

module CASL.CompositionTable.ParseSparQ where

import Text.ParserCombinators.Parsec
import CASL.CompositionTable.CompositionTable
import CASL.CompositionTable.Keywords
import Common.Parsec

import Data.Char

import qualified Control.Monad.Fail as Fail

parseSparQTableOld :: Parser Table
parseSparQTableOld = inParens $ do
  calculusName <- parseCalculusName
  (i1, rs1) <- parseIdBaOths
  ct <- parseConversetable
  (i2, rs2) <- parseIdBaOths
  compt <- parseCompTable
  (i3, rs3) <- parseIdBaOths
  case i1 ++ i2 ++ i3 of
    [i] -> return $ Table
      (Table_Attrs calculusName i $ rs1 ++ rs2 ++ rs3)
      compt ct (Reflectiontable []) $ Models []
    [] -> Fail.fail "missing identity relation"
    is -> Fail.fail $ "non-unique identity relation " ++ show is

parseIdBaOths :: Parser ([Baserel], [Baserel])
parseIdBaOths = fmap (\ l ->
   (concatMap fst l, concatMap snd l))
   $ many parseIdBaOth

parseIdBaOth :: Parser ([Baserel], [Baserel])
parseIdBaOth = try $ do
  s <- cWord
  case () of
    _ | s == identityRelationS
        -> do
            i <- parseRelationId
            return ([i], [])
    _ | s == baseRelationsS
        -> do
            rs <- inParens (many1 parseRelationId)
            return ([], rs)
    _ | elem s [converseOperationS
            , compositionOperationS, homingOperationS, inverseOperationS
            , shortcutOperationS]
        -> pzero
    _ | s == parametricS
        -> forget word >> return ([], [])
    _ -> (skipMany parseQualifierBrace <|> forget cWord)
         >> return ([], [])

parseQualifierBrace :: Parser ()
parseQualifierBrace = do
  string "(" <|> tryString "#'("
  skip
  many $ parseQualifierBrace <|> ((stringLit <|> many1 (noneOf ";()")) >> skip)
  cParenT

cKey :: String -> Parser ()
cKey s = tryString (':' : s) >> skip

cWord :: Parser String
cWord = char ':' >> word

skip :: Parser ()
skip = skipMany $ single space <|> nestedComment ";;#|" ";;|#"
  <|> char ';' <:> many (noneOf "\n")

parseCalculusName :: Parser String
parseCalculusName =
  string "def-calculus" >> skip >> fmap (init . tail) stringLit << skip

word :: Parser String
word = many1 (letter <|> oneOf "_.-?" <|> digit) << skip

oParenT :: Parser ()
oParenT = char '(' >> skip

cParenT :: Parser ()
cParenT = char ')' >> skip

inParens :: Parser a -> Parser a
inParens p = oParenT >> p << cParenT

parseCompTable :: Parser Compositiontable
parseCompTable = cKey compositionOperationS
  >> inParens (fmap Compositiontable parseComptabentryList)

parseComptabentryList :: Parser [Cmptabentry]
parseComptabentryList = many1 parseComptabentry

parseComptabentry :: Parser Cmptabentry
parseComptabentry = inParens $ do
  rel1 <- parseRelationId
  rel2 <- parseRelationId
  results <- parseComptabentryResults
  return (Cmptabentry (Cmptabentry_Attrs rel1 rel2) results)

parseComptabentryResults :: Parser [Baserel]
parseComptabentryResults = inParens (many parseRelationId)
  <|> do
    result@(Baserel str) <- parseRelationId
    return $ if map toUpper str == "NIL" then [] else [result]

parseConversetable :: Parser Conversetable
parseConversetable = do
    entry1 <- parseInverse
    entry3 <- parseShortcut
    entry2 <- parseHoming
    return $ Conversetable_Ternary entry1 entry3 entry2
  <|> fmap Conversetable parseConverse

parseConverse :: Parser [Contabentry]
parseConverse = cKey converseOperationS
  >> inParens (many1 parseContabentry)

parseContabentry :: Parser Contabentry
parseContabentry = inParens $ do
  id1 <- parseRelationId
  fmap (Contabentry id1) $
    single parseRelationId <|> parseBracedRelationIds

parseContabentryList :: String -> Parser [Contabentry_Ternary]
parseContabentryList s = cKey s
  >> inParens (many1 parseContabentryTernary)

parseContabentryTernary :: Parser Contabentry_Ternary
parseContabentryTernary = inParens $ do
  id1 <- parseRelationId
  ids <- many1 parseRelationId <|> parseBracedRelationIds
  return (Contabentry_Ternary id1 ids)

parseBracedRelationIds :: Parser [Baserel]
parseBracedRelationIds = inParens $ many1 parseRelationId

parseInverse :: Parser [Contabentry_Ternary]
parseInverse = parseContabentryList inverseOperationS

parseHoming :: Parser [Contabentry_Ternary]
parseHoming = parseContabentryList homingOperationS

parseShortcut :: Parser [Contabentry_Ternary]
parseShortcut = parseContabentryList shortcutOperationS

parseRelationId :: Parser Baserel
parseRelationId =
  fmap Baserel (many1 $ satisfy $ \ c ->
            not (isSpace c) && notElem c "():;#'\"") << skip
