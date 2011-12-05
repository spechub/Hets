{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

RDF syntax parser, based on rdf4h library

-}

module RDF.Parse where

import OWL2.Parse
import OWL2.AS
import RDF.AS
import Text.RDF.Core
import Text.RDF.TriplesGraph
import Text.RDF.NTriplesParser
import System.Process
import GHC.IO.Exception
import System.IO.Unsafe
import qualified Data.ByteString.Lazy.Char8 as B
import Text.ParserCombinators.Parsec
import Data.ByteString.Lazy.Char8 (ByteString)

{- | takes an input file and outputs the n-triples
    representation in the output file -}
convertRDF2Ntriples :: String -> String -> IO GHC.IO.Exception.ExitCode
convertRDF2Ntriples fileIn fileOut =
    system $ "cwm --rdf " ++ fileIn ++ " --ntriples > " ++ fileOut

-- | takes a filename containing n-triples and returns the list of triples
getNtriples :: Monad m => String -> m [Triple]
getNtriples fileIn = do
    let graph = unsafePerformIO $ parseFile NTriplesParser fileIn
            :: Either ParseFailure TriplesGraph
    case graph of
        Right g -> return $ triplesOf g
        Left _ -> fail $ "cannot parse " ++ fileIn

bs2s :: ByteString -> String
bs2s = B.unpack

f2s :: FastString -> String
f2s = reverse . B.unpack . value

-- | converts an IRI from the rdf4h library into our IRIs
parseIRI :: FastString -> IRI
parseIRI fs = let s = f2s fs in case parse uriP "" s of
    Right iri -> if namePrefix iri == "http" then setFull iri else iri
    Left _ -> error $ s ++ ": invalid IRI"

convertNode :: Node -> Either IRI Literal
convertNode node = case node of
    LNode lv -> Right $ case lv of
        PlainL bs -> Literal (bs2s bs) $ Untyped Nothing
        PlainLL bs1 bs2 -> Literal (bs2s bs1) $ Untyped $ Just $ bs2s bs2
        TypedL bs fs ->
            let l = "\"" ++ bs2s bs ++ "\"^^<" ++ f2s fs ++ ">"
            in case parse literal "" l of
                Right lit -> lit
                Left _ -> error $ l ++ ": invalid literal"
    UNode fs -> Left $ parseIRI fs
    BNode fs -> Left $ (parseIRI fs) {iriType = NodeID}
    _ -> Left nullQName

-- | converts a rdf4h triple into our triples
convertTriple :: Triple -> Sentence
convertTriple (Triple s p o) =
    let Left subj = convertNode s
        Left pre = convertNode p
    in Sentence subj pre $ convertNode o

-- | takes a file with n-triples and returns the rdf graph in our syntax
parseNtriples :: Monad m => String -> m RDFGraph
parseNtriples fileIn = do
    gr <- getNtriples fileIn
    return $ RDFGraph $ map convertTriple gr
    
basicSpec = undefined


