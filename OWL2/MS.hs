{-# LANGUAGE DeriveDataTypeable #-}

module OWL2.MS where

import OWL2.AS
import Common.Keywords
import Common.Id (GetRange)

import OWL.Keywords
import OWL.ColonKeywords
import qualified Data.Map as Map
import Data.Typeable

data OntologyDocument = OntologyDocument {
    prefixDeclaration :: PrefixMap,
    mOntology :: MOntology  
} deriving (Typeable, Show, Eq, Ord)

data MOntology = MOntology {
  muri :: OntologyIRI,
  imports :: [ImportIRI],
  ann :: [Annotations],
  ontologyFrame :: [Frame]
} deriving (Typeable, Show, Eq, Ord)

data AnnotatedList a = AnnotatedList [(Annotations, a)]
   deriving (Typeable, Show, Eq, Ord)

{- | annotions are annotedAnnotationList that must be preceded by the keyword
  @Annotations:@ if non-empty
-}
data Annotations = Annotations [(Annotations, Annotation)]
   deriving (Typeable, Show, Eq, Ord)

noAnnos :: Annotations
noAnnos = Annotations []

data Frame 
  = ClassFrame Class [ClassFrameBit]
  | DatatypeFrame Datatype [Annotations] (Maybe (Annotations, DataRange))
  | ObjectPropertyFrame ObjectProperty [ObjectFrameBit]
  | DataPropertyFrame DataProperty [DataFrameBit]
  | IndividualFrame Individual [IndividualBit]
  | AnnotationFrame AnnotationProperty [AnnotationBit]
  | MiscEquivOrDisjointClasses EquivOrDisjoint Annotations [ClassExpression]
  | MiscEquivOrDisjointObjProp EquivOrDisjoint Annotations [ObjectPropertyExpression]
  | MiscEquivOrDisjointDataProp EquivOrDisjoint Annotations [DataPropertyExpression]
  | MiscSameOrDifferent SameOrDifferent Annotations [Individual]
  deriving (Typeable, Show, Eq, Ord)

data ClassFrameBit
  = ClassAnnotations Annotations  -- nonEmpty list
  | ClassSubClassOf (AnnotatedList ClassExpression)   -- nonEmpty list
  | ClassEquivOrDisjoint EquivOrDisjoint (AnnotatedList ClassExpression) --nonEmpty list
  | ClassDisjointUnion Annotations [ClassExpression] -- min 2 class expressions
  | ClassHasKey Annotations [ObjectPropertyExpression] [DataPropertyExpression]
  deriving (Typeable, Show, Eq, Ord)

data ObjectFrameBit
  = ObjectAnnotations Annotations
  | ObjectDomainOrRange ObjDomainOrRange (AnnotatedList ClassExpression)
  | ObjectCharacteristics (AnnotatedList Character)
  | ObjectEquivOrDisjoint EquivOrDisjoint (AnnotatedList ObjectPropertyExpression)
  | ObjectInverse (AnnotatedList ObjectPropertyExpression)
  | ObjectSubPropertyChain Annotations [ObjectPropertyExpression]
  | ObjectSubPropertyOf (AnnotatedList ObjectPropertyExpression)
  deriving (Typeable, Show, Eq, Ord)

data DataFrameBit
  = DataAnnotations Annotations
  | DataPropDomain (AnnotatedList ClassExpression)
  | DataPropRange (AnnotatedList DataRange)
  | DataFunctional Annotations
  | DataSubPropertyOf (AnnotatedList DataPropertyExpression)
  | DataEquivOrDisjoint EquivOrDisjoint (AnnotatedList DataPropertyExpression)
  deriving (Typeable, Show, Eq, Ord)

data IndividualBit
  = IndividualAnnotations Annotations
  | IndividualTypes (AnnotatedList ClassExpression)
  | IndividualFacts (AnnotatedList Fact)
  | IndividualSameOrDifferent SameOrDifferent (AnnotatedList Individual)
  deriving (Typeable, Show, Eq, Ord)

data Fact
  = ObjectPropertyFact PositiveOrNegative ObjectPropertyExpression Individual
  | DataPropertyFact PositiveOrNegative DataPropertyExpression Literal
  deriving (Typeable, Show, Eq, Ord)

data AnnotationBit
  = AnnotationAnnotations Annotations
  | AnnotationDOR AnnotationDomainOrRange (AnnotatedList IRI)
  | AnnotationSubPropertyOf (AnnotatedList AnnotationProperty)
  deriving (Typeable, Show, Eq, Ord)

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








