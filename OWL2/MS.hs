{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

This module defines all the data types for the Manchester Syntax
of OWL 2
It is modeled after the W3C document:
<http://www.w3.org/TR/owl2-manchester-syntax/>
-}

module OWL2.MS where

import OWL2.AS
import qualified Data.Map as Map

data OntologyDocument = OntologyDocument {
    prefixDeclaration :: PrefixMap,
    mOntology :: MOntology  
} deriving (Show, Eq, Ord)

data MOntology = MOntology {
  muri :: OntologyIRI,
  imports :: [ImportIRI],
  ann :: [Annotations],
  ontologyFrame :: [Frame]
} deriving (Show, Eq, Ord)

data AnnotatedList a = AnnotatedList [(Annotations, a)]
   deriving (Show, Eq, Ord)

{- | annotions are annotedAnnotationList that must be preceded by the keyword
  @Annotations:@ if non-empty
-}
data Annotations = Annotations [(Annotations, Annotation)]
   deriving (Show, Eq, Ord)

noAnnos :: Annotations
noAnnos = Annotations []

data Frame 
  = ClassFrame Class [ClassFrameBit]
  | DatatypeFrame Datatype [Annotations] (Maybe (Annotations, DataRange)) [Annotations]
  | ObjectPropertyFrame ObjectProperty [ObjectFrameBit]
  | DataPropertyFrame DataProperty [DataFrameBit]
  | IndividualFrame Individual [IndividualBit]
  | AnnotationFrame AnnotationProperty [AnnotationBit]
  | MiscEquivOrDisjointClasses EquivOrDisjoint Annotations [ClassExpression]
  | MiscEquivOrDisjointObjProp EquivOrDisjoint Annotations [ObjectPropertyExpression]
  | MiscEquivOrDisjointDataProp EquivOrDisjoint Annotations [DataPropertyExpression]
  | MiscSameOrDifferent SameOrDifferent Annotations [Individual]
  deriving (Show, Eq, Ord)

data ClassFrameBit
  = ClassAnnotations Annotations  -- nonEmpty list
  | ClassSubClassOf (AnnotatedList ClassExpression)   -- nonEmpty list
  | ClassEquivOrDisjoint EquivOrDisjoint (AnnotatedList ClassExpression) --nonEmpty list
  | ClassDisjointUnion Annotations [ClassExpression] -- min 2 class expressions
  | ClassHasKey Annotations [ObjectPropertyExpression] [DataPropertyExpression]
  deriving (Show, Eq, Ord)

data ObjectFrameBit
  = ObjectAnnotations Annotations
  | ObjectDomainOrRange ObjDomainOrRange (AnnotatedList ClassExpression)
  | ObjectCharacteristics (AnnotatedList Character)
  | ObjectEquivOrDisjoint EquivOrDisjoint (AnnotatedList ObjectPropertyExpression)
  | ObjectInverse (AnnotatedList ObjectPropertyExpression)
  | ObjectSubPropertyChain Annotations [ObjectPropertyExpression]
  | ObjectSubPropertyOf (AnnotatedList ObjectPropertyExpression)
  deriving (Show, Eq, Ord)

data DataFrameBit
  = DataAnnotations Annotations
  | DataPropDomain (AnnotatedList ClassExpression)
  | DataPropRange (AnnotatedList DataRange)
  | DataFunctional Annotations
  | DataSubPropertyOf (AnnotatedList DataPropertyExpression)
  | DataEquivOrDisjoint EquivOrDisjoint (AnnotatedList DataPropertyExpression)
  deriving (Show, Eq, Ord)

data IndividualBit
  = IndividualAnnotations Annotations
  | IndividualTypes (AnnotatedList ClassExpression)
  | IndividualFacts (AnnotatedList Fact)
  | IndividualSameOrDifferent SameOrDifferent (AnnotatedList Individual)
  deriving (Show, Eq, Ord)

data Fact
  = ObjectPropertyFact PositiveOrNegative ObjectPropertyExpression Individual
  | DataPropertyFact PositiveOrNegative DataPropertyExpression Literal
  deriving (Show, Eq, Ord)

data AnnotationBit
  = AnnotationAnnotations Annotations
  | AnnotationDOR AnnotationDomainOrRange (AnnotatedList IRI)
  | AnnotationSubPropertyOf (AnnotatedList AnnotationProperty)
  deriving (Show, Eq, Ord)

emptyOntologyDoc :: OntologyDocument
emptyOntologyDoc = OntologyDocument Map.empty emptyOntologyD

emptyOntologyD :: MOntology
emptyOntologyD = MOntology nullQName [] [] []

isEmptyOntologyDoc :: OntologyDocument -> Bool
isEmptyOntologyDoc (OntologyDocument ns onto) =
    Map.null ns && isEmptyOntologyM onto

isEmptyOntologyM :: MOntology -> Bool
isEmptyOntologyM (MOntology (QN _ l _ n) annoList impList frames) =
    null l && null n && null annoList && null impList && null frames
