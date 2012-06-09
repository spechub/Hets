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

import qualified Data.Map as Map

-- * RDF Turtle Document

data TurtleDocument = TurtleDocument
    { prefixMap :: Map.Map String IRI
    , statements :: [Statement] }
    deriving (Show, Eq, Ord)

emptyTurtleDocument :: TurtleDocument
emptyTurtleDocument = TurtleDocument Map.empty []

data Statement = Statement Triples | Prefix String IRI | Base IRI | Comment String
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
  | ObjectLiteral Literal
    deriving (Show, Eq, Ord)

data PredicateObjectList = PredicateObjectList Predicate [Object]
    deriving (Show, Eq, Ord)

-- * Datatypes for Hets manipulation

data Axiom = Axiom Subject Predicate Object
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

