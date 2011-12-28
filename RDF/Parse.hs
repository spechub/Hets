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

import OWL2.AS
import OWL2.Parse
import RDF.AS
import RDF.Symbols

import Text.ParserCombinators.Parsec

-- * ntriples parser

-- | parses an object
parseObj :: CharParser st Object
parseObj = fmap Right literal <|> fmap Left uriP

-- | parses a comment
comment :: CharParser st ()
comment = do
    skipChar '#'
    forget $ manyTill anyChar $ char '\n'

-- | parses one ntriple (subject, predicate, object)
parseNTriple :: CharParser st Axiom
parseNTriple = do
    many space
    subj <- uriP
    pre <- uriP
    obj <- parseObj
    skips $ char '.'
    return $ Axiom subj pre obj

-- | parses a string containing several ntriples
basicSpec :: CharParser st RDFGraph
basicSpec = do
    many $ forget space <|> comment
    fmap RDFGraph $ many parseNTriple

-- | parses an ntriple file
parseNTriplesFile :: String -> IO RDFGraph
parseNTriplesFile file = do
  str <- readFile file
  case runParser (basicSpec << eof) () file str of
    Right g -> return g
    Left err -> error $ show err

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
