{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  Datatypes specific to the Manchester Syntax of OWL 2

References  :  <http://www.w3.org/TR/owl2-manchester-syntax/>
-}

module OWL2.MS where

import OWL2.AS
import Common.Id (GetRange)
import qualified Data.Map as Map

data OntologyDocument = OntologyDocument {
    prefixDeclaration :: PrefixMap,
    mOntology :: MOntology
 } deriving (Show, Eq, Ord)

instance GetRange OntologyDocument

data MOntology = MOntology {
  muri :: OntologyIRI,
  imports :: [ImportIRI],
  ann :: [Annotations],
  ontologyFrame :: [Frame]
 } deriving (Show, Eq, Ord)

{- | annotions are annotedAnnotationList that must be preceded by the keyword
  @Annotations:@ if non-empty -}
type Annotations = [Annotation]

data AnnotatedList a = AnnotatedList { convertAnnList :: [(Annotations, a)] }
   deriving (Show, Eq, Ord)

data Frame
   = Frame Entity [FrameBit]
   | MiscFrame Relation Annotations Misc
   | MiscSameOrDifferent SameOrDifferent Annotations [Individual]
    deriving (Show, Eq, Ord)

data FrameBit
  = AnnotationFrameBit Annotations
  | AnnotationBit Relation (AnnotatedList AnnotationProperty)
  | AnnotationDR DomainOrRange (AnnotatedList IRI)
  | DatatypeBit Annotations DataRange
  | ExpressionBit Relation (AnnotatedList ClassExpression)
  | ClassDisjointUnion Annotations [ClassExpression]
  | ClassHasKey Annotations [ObjectPropertyExpression] [DataPropertyExpression]
  | ObjectBit Relation (AnnotatedList ObjectPropertyExpression)
  | ObjectDomainOrRange DomainOrRange (AnnotatedList ClassExpression)
  | ObjectCharacteristics (AnnotatedList Character)
  | ObjectSubPropertyChain Annotations [ObjectPropertyExpression]
  | DataBit Relation (AnnotatedList DataPropertyExpression)
  | DataPropRange (AnnotatedList DataRange)
  | DataPropDomain (AnnotatedList ClassExpression)
  | DataFunctional Annotations
  | IndividualFacts (AnnotatedList Fact)
  | IndividualSameOrDifferent SameOrDifferent (AnnotatedList Individual)
    deriving (Show, Eq, Ord)

data Misc
  = MiscEquivOrDisjointClasses
      [ClassExpression]
  | MiscEquivOrDisjointObjProp
      [ObjectPropertyExpression]
  | MiscEquivOrDisjointDataProp
      [DataPropertyExpression]
     deriving (Show, Eq, Ord)

data Fact
  = ObjectPropertyFact PositiveOrNegative ObjectPropertyExpression Individual
  | DataPropertyFact PositiveOrNegative DataPropertyExpression Literal
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
