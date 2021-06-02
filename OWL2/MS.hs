{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OWL2/MS.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Datatypes specific to the Manchester Syntax of OWL 2

References  :  <http://www.w3.org/TR/owl2-manchester-syntax/>
-}

module OWL2.MS where

import Common.Id
import Common.IRI
import qualified OWL2.AS as AS

import Data.Data
import qualified Data.Map as Map
import qualified Data.Set as Set

{- | annotions are annotedAnnotationList that must be preceded by the keyword
  @Annotations:@ if non-empty -}
type Annotations = [AS.Annotation]

type AnnotatedList a = [(Annotations, a)]

-- | this datatype extends the Manchester Syntax to also allow GCIs
data Extended =
    Misc Annotations
  | ClassEntity AS.ClassExpression
  | ObjectEntity AS.ObjectPropertyExpression
  | SimpleEntity AS.Entity
    deriving (Show, Eq, Ord, Typeable, Data)

-- | frames with annotated lists
data ListFrameBit =
    AnnotationBit (AnnotatedList AS.AnnotationProperty) -- relation
  | ExpressionBit (AnnotatedList AS.ClassExpression) -- relation
  | ObjectBit (AnnotatedList AS.ObjectPropertyExpression) -- relation
  | DataBit (AnnotatedList AS.DataPropertyExpression) -- relation
  | IndividualSameOrDifferent (AnnotatedList AS.NamedIndividual) -- relation
  | ObjectCharacteristics (AnnotatedList AS.Character)
  | DataPropRange (AnnotatedList AS.DataRange)
  | IndividualFacts (AnnotatedList Fact)
    deriving (Show, Eq, Ord, Typeable, Data)

data AnnoType = Declaration | Assertion | XmlError String
    deriving (Show, Eq, Ord, Typeable, Data)

-- | frames which start with annotations
data AnnFrameBit =
    AnnotationFrameBit AnnoType
  | DataFunctional
  | DatatypeBit AS.DataRange
  | ClassDisjointUnion [AS.ClassExpression]
  | ClassHasKey [AS.ObjectPropertyExpression] [AS.DataPropertyExpression]
  | ObjectSubPropertyChain [AS.ObjectPropertyExpression]
    deriving (Show, Eq, Ord, Typeable, Data)

data Fact =
    ObjectPropertyFact AS.PositiveOrNegative AS.ObjectPropertyExpression AS.NamedIndividual
  | DataPropertyFact AS.PositiveOrNegative AS.DataPropertyExpression AS.Literal
  deriving (Show, Eq, Ord, Typeable, Data)

data FrameBit =
    ListFrameBit (Maybe AS.Relation) ListFrameBit
  | AnnFrameBit Annotations AnnFrameBit
    deriving (Show, Eq, Ord, Typeable, Data)

data Frame = Frame Extended [FrameBit]
    deriving (Show, Eq, Ord, Typeable, Data)

data Axiom = PlainAxiom
  { axiomTopic :: Extended -- the Class or Individual
  , axiomBit :: FrameBit -- the property expressed by the sentence
  } deriving (Show, Eq, Ord, Typeable, Data)

{-

 Individual: alex           <------ axiomTopic
   Facts: hasParent john    <------ axiomBit

-}

mkExtendedEntity :: AS.Entity -> Extended
mkExtendedEntity e@(AS.Entity _ ty iri) = case ty of
  AS.Class -> ClassEntity $ AS.Expression iri
  AS.ObjectProperty -> ObjectEntity $ AS.ObjectProp iri
  _ -> SimpleEntity e

getAxioms :: Frame -> [Axiom]
getAxioms (Frame e fbl) = map (PlainAxiom e) fbl

axToFrame :: Axiom -> Frame
axToFrame (PlainAxiom e fb) = Frame e [fb]

instance GetRange Axiom where
  getRange = Range . joinRanges . map rangeSpan . Set.toList . symsOfAxiom

data Ontology = Ontology
    { name :: AS.OntologyIRI
    , imports :: [AS.ImportIRI]
    , ann :: [Annotations]
    , ontFrames :: [Frame]
    } deriving (Show, Eq, Ord, Typeable, Data)

data OntologyDocument = OntologyDocument
    { prefixDeclaration :: AS.PrefixMap
    , ontology :: Ontology
    } deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange OntologyDocument

emptyOntology :: [Frame] -> Ontology
emptyOntology = Ontology nullIRI [] []

emptyOntologyDoc :: OntologyDocument
emptyOntologyDoc = OntologyDocument Map.empty $ emptyOntology []

isEmptyOntology :: Ontology -> Bool
isEmptyOntology (Ontology oiri annoList impList fs) = isNullIRI oiri
    && null annoList && null impList && null fs

isEmptyOntologyDoc :: OntologyDocument -> Bool
isEmptyOntologyDoc (OntologyDocument ns onto) =
    Map.null ns && isEmptyOntology onto

emptyAnnoList :: [a] -> AnnotatedList a
emptyAnnoList = map $ \ x -> ([], x)

symsOfAxiom :: Axiom -> Set.Set AS.Entity
symsOfAxiom (PlainAxiom e f) = Set.union (symsOfExtended e) $ symsOfFrameBit f

symsOfExtended :: Extended -> Set.Set AS.Entity
symsOfExtended e = case e of
  Misc as -> symsOfAnnotations as
  SimpleEntity s -> Set.singleton s
  ObjectEntity o -> symsOfObjectPropertyExpression o
  ClassEntity c -> symsOfClassExpression c

symsOfObjectPropertyExpression :: AS.ObjectPropertyExpression -> Set.Set AS.Entity
symsOfObjectPropertyExpression o = case o of
  AS.ObjectProp i -> Set.singleton $ AS.mkEntity AS.ObjectProperty i
  AS.ObjectInverseOf i -> symsOfObjectPropertyExpression i

symsOfClassExpression :: AS.ClassExpression -> Set.Set AS.Entity
symsOfClassExpression ce = case ce of
  AS.Expression c -> Set.singleton $ AS.mkEntity AS.Class c
  AS.ObjectJunction _ cs -> Set.unions $ map symsOfClassExpression cs
  AS.ObjectComplementOf c -> symsOfClassExpression c
  AS.ObjectOneOf is -> Set.fromList $ map (AS.mkEntity AS.NamedIndividual) is
  AS.ObjectValuesFrom _ oe c -> Set.union (symsOfObjectPropertyExpression oe)
    $ symsOfClassExpression c
  AS.ObjectHasValue oe i -> Set.insert (AS.mkEntity AS.NamedIndividual i)
    $ symsOfObjectPropertyExpression oe
  AS.ObjectHasSelf oe -> symsOfObjectPropertyExpression oe
  AS.ObjectCardinality (AS.Cardinality _ _ oe mc) -> Set.union
    (symsOfObjectPropertyExpression oe)
    $ maybe Set.empty symsOfClassExpression mc
  AS.DataValuesFrom _ de dr -> Set.union (Set.fromList $ map (AS.mkEntity AS.DataProperty) de)
    $ symsOfDataRange dr
  AS.DataHasValue de _ -> Set.singleton $ AS.mkEntity AS.DataProperty de
  AS.DataCardinality (AS.Cardinality _ _ d m) -> Set.insert (AS.mkEntity AS.DataProperty d)
    $ maybe Set.empty symsOfDataRange m

symsOfDataRange :: AS.DataRange -> Set.Set AS.Entity
symsOfDataRange dr = case dr of
  AS.DataType t _ -> Set.singleton $ AS.mkEntity AS.Datatype t
  AS.DataJunction _ ds -> Set.unions $ map symsOfDataRange ds
  AS.DataComplementOf d -> symsOfDataRange d
  AS.DataOneOf _ -> Set.empty

symsOfAnnotation :: AS.Annotation -> Set.Set AS.Entity
symsOfAnnotation (AS.Annotation as p _) = Set.insert
   (AS.mkEntity AS.AnnotationProperty p) $ Set.unions (map symsOfAnnotation as)

symsOfAnnotations :: Annotations -> Set.Set AS.Entity
symsOfAnnotations = Set.unions . map symsOfAnnotation

symsOfFrameBit :: FrameBit -> Set.Set AS.Entity
symsOfFrameBit fb = case fb of
  ListFrameBit _ lb -> symsOfListFrameBit lb
  AnnFrameBit as af -> Set.union (symsOfAnnotations as) $ symsOfAnnFrameBit af

symsOfAnnFrameBit :: AnnFrameBit -> Set.Set AS.Entity
symsOfAnnFrameBit af = case af of
  AnnotationFrameBit _ -> Set.empty
  DataFunctional -> Set.empty
  DatatypeBit dr -> symsOfDataRange dr
  ClassDisjointUnion cs -> Set.unions $ map symsOfClassExpression cs
  ClassHasKey os ds -> Set.union
    (Set.unions $ map symsOfObjectPropertyExpression os)
    . Set.fromList $ map (AS.mkEntity AS.DataProperty) ds
  ObjectSubPropertyChain os ->
    Set.unions $ map symsOfObjectPropertyExpression os

symsOfListFrameBit :: ListFrameBit -> Set.Set AS.Entity
symsOfListFrameBit lb = case lb of
  AnnotationBit l -> annotedSyms
    (Set.singleton . AS.mkEntity AS.AnnotationProperty) l
  ExpressionBit l -> annotedSyms symsOfClassExpression l
  ObjectBit l -> annotedSyms symsOfObjectPropertyExpression l
  DataBit l -> annotedSyms (Set.singleton . AS.mkEntity AS.DataProperty) l
  IndividualSameOrDifferent l -> annotedSyms
    (Set.singleton . AS.mkEntity AS.NamedIndividual) l
  ObjectCharacteristics l -> annotedSyms (const Set.empty) l
  DataPropRange l -> annotedSyms symsOfDataRange l
  IndividualFacts l -> annotedSyms symsOfFact l

symsOfFact :: Fact -> Set.Set AS.Entity
symsOfFact fact = case fact of
  ObjectPropertyFact _ oe i -> Set.insert (AS.mkEntity AS.NamedIndividual i)
    $ symsOfObjectPropertyExpression oe
  DataPropertyFact _ d _ -> Set.singleton $ AS.mkEntity AS.DataProperty d

annotedSyms :: (a -> Set.Set AS.Entity) -> AnnotatedList a -> Set.Set AS.Entity
annotedSyms f l = Set.union (Set.unions $ map (symsOfAnnotations . fst) l)
  . Set.unions $ map (f . snd) l
