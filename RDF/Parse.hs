{- |
Module      :  $Header$
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

import OWL2.AS
import OWL2.Parse hiding (stringLiteral, literal, skips)
import RDF.AS
import RDF.Symbols

import Network.URI
import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

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

longLiteral :: CharParser st String
longLiteral = do
    string "\"\"\""
    ls <- flat $ many $ single (noneOf "\"")
    string "\"\"\""
    return $ '\n' : ls
    
stringLiteral :: CharParser st Literal
stringLiteral = do
  s <- try longLiteral <|> fmap rmQuotes stringLit
  do
      string cTypeS
      d <- datatypeUri
      return $ Literal s $ Typed d
    <|> do
        string "@"
        t <- skips $ optionMaybe languageTag
        return $ Literal s $ Untyped t
    <|> skips (return $ Literal s $ Typed $ mkQName "string")

literal :: CharParser st Literal
literal = do
    f <- skips $ try floatingPointLit
         <|> fmap decToFloat decimalLit
    return $ NumberLit f
  <|> stringLiteral

parseBase :: CharParser st Statement
parseBase = do
    pkeyword "@base"
    base <- skips uriQ
    skips $ char '.'
    return $ Base base

parsePrefix :: CharParser st Statement
parsePrefix = do
    pkeyword "@prefix"
    p <- skips (option "" prefix << char ':')
    i <- skips uriQ
    skips $ char '.'
    return $ Prefix p i

parsePredicate :: CharParser st Predicate
parsePredicate = fmap Predicate $ skips uriQ

parseSubject :: CharParser st Subject
parseSubject =
    fmap Subject (skips uriQ)
  <|> fmap SubjectList
            (between (skips $ char '[') (skips $ char ']') $ skips parsePredObjList)
  <|> fmap SubjectCollection
            (between (skips $ char '(') (skips $ char ')') $ many parseObject)

parseObject :: CharParser st Object
parseObject = fmap ObjectLiteral literal <|> fmap Object parseSubject

parsePredObjects :: CharParser st PredicateObjectList
parsePredObjects = do
    pred <- parsePredicate
    objs <- sepBy parseObject $ skips $ char ','
    return $ PredicateObjectList pred objs

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
parseStatement = parseBase <|> parsePrefix <|> fmap Statement parseTriples

extractPrefixMap :: [Statement] -> Map.Map String IRI
extractPrefixMap ls = case ls of
    [] -> Map.empty
    h : t -> case h of
        Prefix p iri -> Map.insert p iri $ extractPrefixMap t
        _ -> extractPrefixMap t

basicSpec :: CharParser st TurtleDocument
basicSpec = do
    many parseComment
    ls <- many parseStatement
    return $ TurtleDocument (extractPrefixMap ls) ls

