{- |
Module      :  $Header$
Copyright   :  (c) Francisc-Nicolae Bungiu
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

RDF abstract syntax

References: 
    <http://www.informatik.uni-bremen.de/~till/papers/ontotrans.pdf>
    <http://www.w3.org/TR/rdf-concepts/#section-Graph-syntax>
-}

module RDF.AS where

import OWL2.AS
import Common.Id

import qualified Data.Map as Map

-- * Graphs

type Subject = IRI
type Predicate = IRI
type Object = Either IRI Literal

-- Sentence represents a RDF Triple
data Sentence = Sentence Subject Predicate Object
    deriving (Show, Eq, Ord)

data RDFGraph = RDFGraph [Sentence]
    deriving (Show, Eq, Ord)

data RDFEntityType = Subject | Predicate | Object
    deriving (Show, Eq, Ord)

data EntityRDF = EntityRDF RDFEntityType IRI
    deriving (Show, Eq, Ord)

type StringMap = Map.Map String String
type MorphMap = Map.Map EntityRDF IRI

instance GetRange RDFGraph where
