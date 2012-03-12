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

parse1Base :: CharParser st BaseIRI
parse1Base = do
    pkeyword "@base"
    base <- skips uriQ
    skips $ string "."
    return $ BaseIRI base

parse1Prefix :: CharParser st Prefix
parse1Prefix = do
    pkeyword "@prefix"
    p <- skips (option "" prefix << char ':')
    i <- skips fullIri
    skips $ string "."
    return $ Prefix p i

parse1BaseOrPrefix :: CharParser st (Either BaseIRI Prefix)
parse1BaseOrPrefix = fmap Left parse1Base <|> fmap Right parse1Prefix

startsWithScheme :: IRI -> Bool
startsWithScheme iri = isPrefixOf "//" $ localPart iri

baseStartsWithScheme :: BaseIRI -> Bool
baseStartsWithScheme (BaseIRI iri) = startsWithScheme iri

appendTwoBases :: BaseIRI -> BaseIRI -> BaseIRI
appendTwoBases (BaseIRI b1) (BaseIRI b2) =
    let lpb1 = localPart b1
        (lp1, ok) = if last lpb1 == '/' then (lpb1, 1) else (lpb1 ++ "/", 0)
        lp = lp1 ++ localPart b2
        exp = if ok == 0 then expandedIRI b1 ++ "/" else expandedIRI b1
    in BaseIRI $ b1 {localPart = lp, expandedIRI = exp ++ localPart b2}

resolveIRI :: BaseIRI -> IRI -> IRI
resolveIRI b iri = extractIRI $ appendTwoBases b $ BaseIRI iri

extractIRI :: BaseIRI -> IRI
extractIRI (BaseIRI b) = b

parseBases :: BaseIRI -> TurtlePrefixMap -> CharParser st (BaseIRI, TurtlePrefixMap)
parseBases base pm = do
    e <- parse1BaseOrPrefix
    case e of
        Left b ->
            if baseStartsWithScheme b || iriType (extractIRI b) /= Full then parseBases b pm
            else parseBases (appendTwoBases base b) pm
        Right p@(Prefix s iri) ->
            if startsWithScheme iri then parseBases base $ Map.insert s iri pm
            else parseBases base $ Map.insert s (resolveIRI base iri) pm
   <|> return (base, pm)

parseIRI :: BaseIRI -> CharParser st IRI
parseIRI b = do
    iri <- uriQ
    return $ if iriType iri == Full && not (startsWithScheme iri)
        then resolveIRI b iri else iri

parseTerm :: BaseIRI -> CharParser st Term
parseTerm b = fmap LiteralTerm literal <|> fmap IRITerm (parseIRI b)
     <|> fmap Collection (parensP $ many $ skips $ parseTerm b)


parseTriples :: BaseIRI -> TurtlePrefixMap -> String
    -> CharParser st [(Triple, BaseIRI, TurtlePrefixMap)]
parseTriples base tpm end = do
    (b, pm) <- parseBases base tpm
    t <- case end of
        "." -> do
            s <- skips $ parseTerm b
            p <- skips $ parseTerm b
            o <- skips $ parseTerm b
            return $ NTriple s p o
        "," -> do
            o <- skips $ parseTerm b
            return $ AbbreviatedTriple Nothing o
        ";" -> do
            p <- skips $ parseTerm b
            o <- skips $ parseTerm b
            return $ AbbreviatedTriple (Just p) o
    sep <- choice $ map (\ s -> skips $ string s >> return s) [".", ",", ";"]
    tl <- parseTriples b pm sep
    return $ (t, b, pm) : tl
  <|> return []

      
