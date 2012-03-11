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

import Data.List
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

parse1Base :: CharParser st BaseIRI
parse1Base = do
	skips $ string "@base"
	base <- skips fullIri
	skips $ string "."
	return $ BaseIRI base

parseAndResolveBases :: CharParser st BaseIRI
parseAndResolveBases = do
	bl <- many parse1Base
	return $ resolveBases bl

startsWithScheme :: IRI -> Bool
startsWithScheme iri = isPrefixOf "//" $ localPart iri

baseStartsWithScheme :: BaseIRI -> Bool
baseStartsWithScheme (BaseIRI iri) = startsWithScheme iri

resolveBases :: [BaseIRI] -> BaseIRI
resolveBases ls = if null ls then BaseIRI dummyQName else
	let h : t = ls
	in if null $ filter baseStartsWithScheme t
		then appendAllBases ls
		else resolveBases t
	
appendTwoBases :: BaseIRI -> BaseIRI -> BaseIRI
appendTwoBases (BaseIRI b1) (BaseIRI b2) =
	let lp = localPart b1 ++ localPart b2
	in BaseIRI $ b1 {localPart = lp}
	
appendAllBases :: [BaseIRI] -> BaseIRI
appendAllBases bl = foldl1 appendTwoBases bl
