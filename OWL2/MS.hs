{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

    Datatypes specific to the Manchester Syntax of OWL 2

References  :  <http://www.w3.org/TR/owl2-manchester-syntax/>
-}

module OWL2.MS where

import Common.Id (GetRange)
import OWL2.AS
import qualified Data.Map as Map

{- | annotions are annotedAnnotationList that must be preceded by the keyword
  @Annotations:@ if non-empty -}
type Annotations = [Annotation]

type AnnotatedList a = [(Annotations, a)]

-- | this datatype extends the Manchester Syntax to also allow GCIs
data Extended
  = Misc Annotations
  | SimpleEntity Entity
  | ObjectEntity ObjectPropertyExpression
  | ClassEntity ClassExpression
    deriving (Show, Eq, Ord)

-- | frames with annotated lists
data ListFrameBit
  = AnnotationBit (AnnotatedList AnnotationProperty) -- relation
  | ExpressionBit (AnnotatedList ClassExpression) -- relation
  | ObjectBit (AnnotatedList ObjectPropertyExpression) -- relation
  | DataBit (AnnotatedList DataPropertyExpression) -- relation
  | IndividualSameOrDifferent (AnnotatedList Individual) -- relation
  | ObjectCharacteristics (AnnotatedList Character)
  | DataPropRange (AnnotatedList DataRange)
  | IndividualFacts (AnnotatedList Fact)
    deriving (Show, Eq, Ord)

-- | frames which start with annotations
data AnnFrameBit
  = AnnotationFrameBit
  | DataFunctional
  | DatatypeBit DataRange
  | ClassDisjointUnion [ClassExpression]
  | ClassHasKey [ObjectPropertyExpression] [DataPropertyExpression]
  | ObjectSubPropertyChain [ObjectPropertyExpression]
    deriving (Show, Eq, Ord)

data Fact
  = ObjectPropertyFact PositiveOrNegative ObjectPropertyExpression Individual
  | DataPropertyFact PositiveOrNegative DataPropertyExpression Literal
  deriving (Show, Eq, Ord)

data FrameBit
  = ListFrameBit (Maybe Relation) ListFrameBit
  | AnnFrameBit Annotations AnnFrameBit
    deriving (Show, Eq, Ord)

data Frame = Frame Extended [FrameBit]
    deriving (Show, Eq, Ord)

data Axiom = PlainAxiom Extended FrameBit
    deriving (Show, Eq, Ord)

getAxioms :: Frame -> [Axiom]
getAxioms (Frame e fbl) = map (PlainAxiom e) fbl

axToFrame :: Axiom -> Frame
axToFrame (PlainAxiom e fb) = Frame e [fb]

instance GetRange Axiom

data Ontology = Ontology {
  name :: OntologyIRI,
  imports :: [ImportIRI],
  ann :: [Annotations],
  ontFrames :: [Frame]
 } deriving (Show, Eq, Ord)

data OntologyDocument = OntologyDocument {
    prefixDeclaration :: PrefixMap,
    ontology :: Ontology
 } deriving (Show, Eq, Ord)

instance GetRange OntologyDocument

emptyOnt :: Ontology
emptyOnt = Ontology nullQName [] [] []

emptyDoc :: OntologyDocument
emptyDoc = OntologyDocument Map.empty emptyOnt

emptyOntologyDoc :: OntologyDocument
emptyOntologyDoc = OntologyDocument Map.empty emptyOntologyD

emptyOntologyD :: Ontology
emptyOntologyD = Ontology nullQName [] [] []

isEmptyOntologyDoc :: OntologyDocument -> Bool
isEmptyOntologyDoc (OntologyDocument ns onto) =
    Map.null ns && isEmptyOntology onto

isEmptyOntology :: Ontology -> Bool
isEmptyOntology (Ontology (QN _ l _ n _) annoList impList fs) =
    null l && null n && null annoList && null impList && null fs
