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

-- | the datatype for Manchester Syntax frames
data Frame = Frame (Either Annotations Entity) [FrameBit]
    deriving (Show, Eq, Ord)

data Axiom = PlainAxiom (Either Annotations Entity) FrameBit
    deriving (Show, Eq, Ord)

getAxioms :: Frame -> [Axiom]
getAxioms (Frame e fbl) = map (\fb -> PlainAxiom e fb) fbl

instance GetRange Axiom

data FrameBit
  = ListFrameBit (Maybe Relation) ListFrameBit
  | AnnFrameBit Annotations AnnFrameBit
    deriving (Show, Eq, Ord)

data ListFrameBit
  = AnnotationBit (AnnotatedList AnnotationProperty) --relation
  | ExpressionBit (AnnotatedList ClassExpression) -- relation
  | ObjectBit (AnnotatedList ObjectPropertyExpression) -- relation
  | DataBit (AnnotatedList DataPropertyExpression) -- relation
  | IndividualSameOrDifferent (AnnotatedList Individual) -- relation
  | ObjectCharacteristics (AnnotatedList Character)
  | DataPropRange (AnnotatedList DataRange)
  | IndividualFacts (AnnotatedList Fact)
    deriving (Show, Eq, Ord)

data AnnFrameBit
  = AnnotationFrameBit
  | DataFunctional
  | DatatypeBit DataRange
  | ClassDisjointUnion [ClassExpression]
  | ClassHasKey [ObjectPropertyExpression] [DataPropertyExpression]  
          -- needs to be replaced later on by GCIClassHasKey
  | ObjectSubPropertyChain [ObjectPropertyExpression]
  | GCISubClassOf ClassExpression ClassExpression
  | GCIClassHasKey ClassExpression
        [ObjectPropertyExpression] [DataPropertyExpression]
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
