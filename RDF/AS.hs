{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance, Francisc-Nicolae Bungiu
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

RDF abstract syntax

References:
    <http://www.w3.org/TeamSubmission/turtle/>
    <http://www.informatik.uni-bremen.de/~till/papers/ontotrans.pdf>
    <http://www.w3.org/TR/rdf-concepts/#section-Graph-syntax>
-}

module RDF.AS where

import Common.Id
import OWL2.AS

import Data.List
import qualified Data.Map as Map

-- * RDF Turtle Document

type RDFPrefixMap = Map.Map String IRI

data TurtleDocument = TurtleDocument
    { documentName :: IRI
    , prefixMap :: RDFPrefixMap
    , statements :: [Statement] }
    deriving (Show, Eq, Ord)

emptyTurtleDocument :: TurtleDocument
emptyTurtleDocument = TurtleDocument nullQName Map.empty []

extractTripleStatements :: [Statement] -> [Triples]
extractTripleStatements ls = case ls of
    [] -> []
    h : t -> case h of
        Statement triple -> triple : extractTripleStatements t
        _ -> extractTripleStatements t
        
triplesOfDocument :: TurtleDocument -> [Triples]
triplesOfDocument doc = extractTripleStatements $ statements doc

rdfFirst :: IRI
rdfFirst = QN "rdf" "first" Abbreviated
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#first" nullRange

rdfRest :: IRI
rdfRest = QN "rdf" "rest" Abbreviated
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest" nullRange
    
rdfNil :: IRI
rdfNil = QN "rdf" "nil" Abbreviated
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil" nullRange

data Statement = Statement Triples | PrefixStatement Prefix | BaseStatement Base
    deriving (Show, Eq, Ord)
    
data Prefix = Prefix String IRI
    deriving (Show, Eq, Ord)
    
data Base = Base IRI
    deriving (Show, Eq, Ord)

data Triples = Triples Subject [PredicateObjectList]
    deriving (Show, Eq, Ord)

data Subject =
    Subject IRI
  | SubjectList [PredicateObjectList]
  | SubjectCollection [Object]
    deriving (Show, Eq, Ord)

data Predicate = Predicate IRI
    deriving (Show, Eq, Ord)

data Object = Object Subject
  | ObjectLiteral RDFLiteral
    deriving (Show, Eq, Ord)

data PredicateObjectList = PredicateObjectList Predicate [Object]
    deriving (Show, Eq, Ord)
    
data RDFLiteral = RDFLiteral Bool LexicalForm TypedOrUntyped
  | RDFNumberLit FloatLit
    deriving (Show, Eq, Ord)

-- * Datatypes for Hets manipulation

data Axiom = Axiom IRI IRI (Either IRI RDFLiteral)
    deriving (Show, Eq, Ord)

data RDFEntityType = SubjectEntity | PredicateEntity | ObjectEntity
    deriving (Show, Eq, Ord, Bounded, Enum)

-- | entities used for morphisms
data RDFEntity = RDFEntity RDFEntityType IRI
    deriving (Show, Eq, Ord)

rdfEntityTypes :: [RDFEntityType]
rdfEntityTypes = [minBound .. maxBound]

instance GetRange TurtleDocument where
instance GetRange Axiom where

isAbsoluteIRI :: IRI -> Bool
isAbsoluteIRI iri = iriType iri == Full && (isPrefixOf "//" $ localPart iri)

