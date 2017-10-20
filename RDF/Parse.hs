{- |
Module      :  ./RDF/Parse.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

RDF syntax parser
-}

module RDF.Parse where

import Common.Parsec
import Common.Lexer
import Common.AnnoParser (newlineOrEof)
import Common.Token (criticalKeywords)
import Common.Id
import Common.IRI
import qualified Common.GlobalAnnotations as GA (PrefixMap)

import OWL2.AS
import OWL2.Parse hiding (stringLiteral, literal, skips, uriP)
import RDF.AS
import RDF.Symbols

import Data.Either
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

uriP :: CharParser st IRI
uriP =
  skips $ try $ checkWithUsing showIRI uriQ $ \ q ->
    not (null $ prefixName q) || notElem (abbrevPath q) criticalKeywords

-- * hets symbols parser

rdfEntityType :: CharParser st RDFEntityType
rdfEntityType = choice $ map (\ f -> keyword (show f) >> return f)
  rdfEntityTypes

{- | parses an entity type (subject, predicate or object) followed by a
comma separated list of IRIs -}
rdfSymbItems :: GenParser Char st SymbItems
rdfSymbItems = do
    ext <- optionMaybe rdfEntityType
    iris <- rdfSymbs
    return $ SymbItems ext iris

-- | parse a comma separated list of uris
rdfSymbs :: GenParser Char st [IRI]
rdfSymbs = uriP >>= \ u -> do
    commaP `followedWith` uriP
    us <- rdfSymbs
    return $ u : us
  <|> return [u]

-- | parse a possibly kinded list of comma separated symbol pairs
rdfSymbMapItems :: GenParser Char st SymbMapItems
rdfSymbMapItems = do
  ext <- optionMaybe rdfEntityType
  iris <- rdfSymbPairs
  return $ SymbMapItems ext iris

-- | parse a comma separated list of uri pairs
rdfSymbPairs :: GenParser Char st [(IRI, Maybe IRI)]
rdfSymbPairs = uriPair >>= \ u -> do
    commaP `followedWith` uriP
    us <- rdfSymbPairs
    return $ u : us
  <|> return [u]

-- * turtle syntax parser

skips :: CharParser st a -> CharParser st a
skips = (<< skipMany
        (forget space <|> parseComment <|> nestCommentOut <?> ""))

charOrQuoteEscape :: CharParser st String
charOrQuoteEscape = try (string "\\\"") <|> fmap return anyChar

longLiteral :: CharParser st (String, Bool)
longLiteral = do
    string "\"\"\""
    ls <- flat $ manyTill charOrQuoteEscape $ try $ string "\"\"\""
    return (ls, True)

shortLiteral :: CharParser st (String, Bool)
shortLiteral = do
    char '"'
    ls <- flat $ manyTill charOrQuoteEscape $ try $ string "\""
    return (ls, False)

stringLiteral :: CharParser st RDFLiteral
stringLiteral = do
  (s, b) <- try longLiteral <|> shortLiteral
  do
      string cTypeS
      d <- datatypeUri
      return $ RDFLiteral b s $ Typed d
    <|> do
        string "@"
        t <- skips $ optionMaybe languageTag
        return $ RDFLiteral b s $ Untyped t
    <|> skips (return $ RDFLiteral b s $ Typed $ mkIRI "string")

literal :: CharParser st RDFLiteral
literal = do
    f <- skips $ try floatingPointLit
         <|> fmap decToFloat decimalLit
    return $ RDFNumberLit f
  <|> stringLiteral

parseBase :: CharParser st Base
parseBase = do
    pkeyword "@base"
    base <- skips uriP
    skips $ char '.'
    return $ Base base

parsePrefix :: CharParser st Prefix
parsePrefix = do
    pkeyword "@prefix"
    p <- skips (option "" prefix << char ':')
    i <- skips uriP
    skips $ char '.'
    return $ PrefixR p i

parsePredicate :: CharParser st Predicate
parsePredicate = fmap Predicate $ skips uriP

parseSubject :: CharParser st Subject
parseSubject =
    fmap Subject (skips uriP)
  <|> fmap SubjectList
            (between (skips $ char '[') (skips $ char ']') $ skips parsePredObjList)
  <|> fmap SubjectCollection
            (between (skips $ char '(') (skips $ char ')') $ many parseObject)

parseObject :: CharParser st Object
parseObject = fmap ObjectLiteral literal <|> fmap Object parseSubject

parsePredObjects :: CharParser st PredicateObjectList
parsePredObjects = do
    pr <- parsePredicate
    objs <- sepBy parseObject $ skips $ char ','
    return $ PredicateObjectList pr objs

parsePredObjList :: CharParser st [PredicateObjectList]
parsePredObjList = sepEndBy parsePredObjects $ skips $ char ';'

parseTriples :: CharParser st Triples
parseTriples = do
    s <- parseSubject
    ls <- parsePredObjList
    skips $ char '.'
    return $ Triples s ls

parseComment :: CharParser st ()
parseComment = do
    tryString "#"
    forget $ skips $ manyTill anyChar newlineOrEof

parseStatement :: CharParser st Statement
parseStatement = fmap BaseStatement parseBase
    <|> fmap PrefixStatement parsePrefix <|> fmap Statement parseTriples

basicSpec :: GA.PrefixMap -> CharParser st TurtleDocument
basicSpec pm = do
    many parseComment
    ls <- many parseStatement
    let td = TurtleDocument
             dummyIRI (Map.map mkIRI $ convertPrefixMap pm) ls
-- return $ trace (show $ Map.union predefinedPrefixes (prefixMap td)) td
    return td

predefinedPrefixes :: RDFPrefixMap
predefinedPrefixes = Map.fromList $ zip
    ["rdf", "rdfs", "dc", "owl", "ex", "xsd"]
    $ rights $ map (parse uriQ "")
    [ "<http://www.w3.org/1999/02/22-rdf-syntax-ns#>"
    , "<http://www.w3.org/2000/01/rdf-schema#>"
    , "<http://purl.org/dc/elements/1.1/>"
    , "<http://www.w3.org/2002/07/owl#>"
    , "<http://www.example.org/>"
    , "<http://www.w3.org/2001/XMLSchema#>" ]
