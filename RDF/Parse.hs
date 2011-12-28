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
import OWL2.Parse
import RDF.AS
import System.Process
import Text.ParserCombinators.Parsec

-- | parses an object
parseObj :: CharParser st Object
parseObj = fmap Right literal <|> fmap Left individual

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
