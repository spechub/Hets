{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./RDF/AS.hs
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
import Common.IRI
import OWL2.AS

import Data.Data
import Data.List
import qualified Data.HashMap.Strict as Map

import GHC.Generics (Generic)
import Data.Hashable

-- * RDF Turtle Document

type RDFPrefixMap = Map.HashMap String IRI

data TurtleDocument = TurtleDocument
    { documentName :: IRI
    , prefixMap :: RDFPrefixMap
    , statements :: [Statement] }
    deriving (Show, Eq, Ord, Typeable, Data)

emptyTurtleDocument :: TurtleDocument
emptyTurtleDocument = TurtleDocument nullIRI Map.empty []

data Statement = Statement Triples | PrefixStatement Prefix | BaseStatement Base
    deriving (Show, Eq, Ord, Typeable, Data)

data Prefix = PrefixR String IRI
    deriving (Show, Eq, Ord, Typeable, Data)

data Base = Base IRI
    deriving (Show, Eq, Ord, Typeable, Data)

data Triples = Triples Subject [PredicateObjectList]
    deriving (Show, Eq, Ord, Typeable, Data)

data Subject =
    Subject IRI
  | SubjectList [PredicateObjectList]
  | SubjectCollection [Object]
    deriving (Show, Eq, Ord, Typeable, Data)

data Predicate = Predicate IRI
    deriving (Show, Eq, Ord, Typeable, Data)

data Object = Object Subject
  | ObjectLiteral RDFLiteral
    deriving (Show, Eq, Ord, Typeable, Data)

data PredicateObjectList = PredicateObjectList Predicate [Object]
    deriving (Show, Eq, Ord, Typeable, Data)

data RDFLiteral = RDFLiteral Bool LexicalForm TypedOrUntyped
  | RDFNumberLit FloatLit
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable RDFLiteral

-- * Datatypes for Hets manipulation

data Term =
    SubjectTerm IRI
  | PredicateTerm IRI
  | ObjectTerm (Either IRI RDFLiteral)
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Term

data Axiom = Axiom Term Term Term
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable Axiom

data RDFEntityType = SubjectEntity | PredicateEntity | ObjectEntity
    deriving (Show, Eq, Ord, Bounded, Enum, Typeable, Data, Generic)

instance Hashable RDFEntityType

-- | entities used for morphisms
data RDFEntity = RDFEntity RDFEntityType Term
    deriving (Show, Eq, Ord, Typeable, Data, Generic)

instance Hashable RDFEntity

rdfEntityTypes :: [RDFEntityType]
rdfEntityTypes = [minBound .. maxBound]

instance GetRange TurtleDocument where
instance GetRange RDFEntity where
instance GetRange Axiom where

-- | useful functions

extractTripleStatements :: [Statement] -> [Triples]
extractTripleStatements ls = case ls of
    [] -> []
    h : t -> case h of
        Statement triple -> triple : extractTripleStatements t
        _ -> extractTripleStatements t

triplesOfDocument :: TurtleDocument -> [Triples]
triplesOfDocument doc = extractTripleStatements $ statements doc

rdfFirst :: IRI
rdfFirst = nullIRI { prefixName = "rdf"
                   , iriPath = stringToId "first"
                   , isAbbrev = True }

rdfRest :: IRI
rdfRest = nullIRI { prefixName = "rdf"
                  , iriPath = stringToId "rest"
                  , isAbbrev = True }

rdfNil :: IRI
rdfNil = nullIRI { prefixName = "rdf"
                 , iriPath = stringToId "nil"
                 , isAbbrev = True }

isAbsoluteIRI :: IRI -> Bool
isAbsoluteIRI i = hasFullIRI i && isPrefixOf "//" (show $ iriPath i)

