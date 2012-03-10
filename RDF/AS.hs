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

-- * Graphs

data Term =
    IRITerm IRI
  | LiteralTerm Literal 
  | Collection [IRI]
  deriving (Show, Eq, Ord)

type Subject = Term
type Predicate = Term
type Object = Term
  
data Triple =
      NTriple Subject Predicate Object
    | AbbreviatedTriple Subject [(Maybe Predicate, Object)]
    deriving (Show, Eq, Ord)

data BaseIRI = Base IRI
    deriving (Show, Eq, Ord)

data Prefix = Prefix String IRI
    deriving (Show, Eq, Ord)
    
data Axiom = Axiom Subject Predicate Object
    deriving (Show, Eq, Ord)
    
data TurtleDocument = TurtleDocument
    { prefixMap :: Map.Map String IRI
    , triples :: [Triple] 
    } deriving (Show, Eq, Ord)
    
data RDFEntityType = Subject | Predicate | Object
    deriving (Show, Eq, Ord, Bounded, Enum)

-- | entities used for morphisms
data RDFEntity = RDFEntity RDFEntityType IRI
    deriving (Show, Eq, Ord)

rdfEntityTypes :: [RDFEntityType]
rdfEntityTypes = [minBound .. maxBound]

instance GetRange TurtleDocument where
instance GetRange Axiom where
instance GetRange RDFEntity where
