{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(deriving Typeable)

Contains    :  Datatypes specific to the Functional Syntax of OWL 2

References  :  <http://www.w3.org/TR/2009/REC-owl2-syntax-20091027/#Functional-Style_Syntax>
-}

module OWL2.FS where

import Common.Id (GetRange)

import OWL2.AS
import qualified Data.Map as Map

------------------------
-- ONTOLOGIES SYNTAX
------------------------

data OntologyFile = OntologyFile
  { prefixName :: PrefixMap
  , ontology :: Ontology
  } deriving (Show, Eq, Ord)

instance GetRange OntologyFile

data Ontology = Ontology
  { uri :: OntologyIRI
  , importsList :: [ImportIRI]
  , annotationsList :: [Annotation]
  , axiomsList :: [Axiom]
  } deriving (Show, Eq, Ord)

type OntologyMap = Map.Map String OntologyFile

---------------------
-- AXIOMS
---------------------

data Axiom = -- Annotations can be ignored
    PlainAxiom [Annotation] PlainAxiom
  | EntityAnno AnnotationAxiom
    deriving (Show, Eq, Ord)

instance GetRange Axiom

data PlainAxiom =
    SubClassOf SubClass SuperClass
  | EquivOrDisjointClasses Relation [ClassExpression] -- min. 2 desc.
  | DisjointUnion Class [ClassExpression] -- min. 2 desc.
  | SubObjectPropertyOf SubObjectPropertyExpression ObjectPropertyExpression
  | EquivOrDisjointObjectProperties Relation [ObjectPropertyExpression]  -- min. 2  ObjectPropertyExpression
  | ObjectPropertyDomainOrRange Relation ObjectPropertyExpression ClassExpression
  | InverseObjectProperties ObjectPropertyExpression ObjectPropertyExpression
  | ObjectPropertyCharacter Character ObjectPropertyExpression
  | SubDataPropertyOf DataPropertyExpression DataPropertyExpression
  | EquivOrDisjointDataProperties Relation [DataPropertyExpression] -- min. 2 DataPropertyExpressions
  | DataPropertyDomainOrRange DataDomainOrRange DataPropertyExpression
  | FunctionalDataProperty DataPropertyExpression
  | SameOrDifferentIndividual SameOrDifferent [Individual] -- min. 2 ind.
  | ClassAssertion ClassExpression Individual 	-- arguments are reversed from OWL-1
  | ObjectPropertyAssertion (Assertion ObjectPropertyExpression TargetIndividual)
  | DataPropertyAssertion (Assertion DataPropertyExpression TargetValue)
  | Declaration Entity
  | DatatypeDefinition Datatype DataRange
  | HasKey ClassExpression [ObjectPropertyExpression] [DataPropertyExpression]
    deriving (Show, Eq, Ord)

type SubClass = ClassExpression
type SuperClass = ClassExpression

data Assertion a b = Assertion a PositiveOrNegative SourceIndividual b
    deriving (Show, Eq, Ord)

---------------------
-- ONTOLOGY FILES
---------------------

emptyOntologyFile :: OntologyFile
emptyOntologyFile = OntologyFile Map.empty emptyOntology

emptyOntologyByName :: QName -> Ontology
emptyOntologyByName qn = Ontology qn [] [] []

emptyOntology :: Ontology
emptyOntology = emptyOntologyByName nullQName

isEmptyOntologyFile :: OntologyFile -> Bool
isEmptyOntologyFile (OntologyFile ns onto) =
    Map.null ns && isEmptyOntology onto

isEmptyOntology :: Ontology -> Bool
isEmptyOntology (Ontology (QN _ l _ n) annoList impList axioms) =
    null l && null n && null annoList && null impList && null axioms

