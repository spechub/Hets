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

{- | takes an input file and outputs the n-triples
    representation in the output file -}
convertRDF2Ntriples :: String -> String -> IO ()
convertRDF2Ntriples fileIn fileOut = do
    system $ "cwm --rdf " ++ fileIn ++ " --ntriples > " ++ fileOut
    return ()

-- parses and object
parseObj :: CharParser st Object
parseObj = fmap Right literal <|> fmap Left individual

comment :: CharParser st ()
comment = do
    skipChar '#'
    forget $ manyTill anyChar $ char '\n'

parseTriple :: CharParser st Axiom
parseTriple = do
    many space
    subj <- uriP
    pre <- uriP
    obj <- parseObj
    skips $ char '.'
    return $ Axiom subj pre obj

parseNtriples :: String -> IO RDFGraph
parseNtriples file = do
  str <- readFile file
  case runParser (basicSpec << eof) () file str of
    Right g -> return g
    Left err -> error $ show err

basicSpec :: CharParser st RDFGraph
basicSpec = do
    many $ forget space <|> comment
    fmap RDFGraph $ many parseTriple

