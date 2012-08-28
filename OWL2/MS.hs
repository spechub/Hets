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

import Common.Id
import OWL2.AS
import qualified Data.Map as Map
import qualified Data.Set as Set

{- | annotions are annotedAnnotationList that must be preceded by the keyword
  @Annotations:@ if non-empty -}
type Annotations = [Annotation]

type AnnotatedList a = [(Annotations, a)]

-- | this datatype extends the Manchester Syntax to also allow GCIs
data Extended =
    Misc Annotations
  | ClassEntity ClassExpression
  | ObjectEntity ObjectPropertyExpression
  | SimpleEntity Entity
    deriving (Show, Eq, Ord)

-- | frames with annotated lists
data ListFrameBit =
    AnnotationBit (AnnotatedList AnnotationProperty) -- relation
  | ExpressionBit (AnnotatedList ClassExpression) -- relation
  | ObjectBit (AnnotatedList ObjectPropertyExpression) -- relation
  | DataBit (AnnotatedList DataPropertyExpression) -- relation
  | IndividualSameOrDifferent (AnnotatedList Individual) -- relation
  | ObjectCharacteristics (AnnotatedList Character)
  | DataPropRange (AnnotatedList DataRange)
  | IndividualFacts (AnnotatedList Fact)
    deriving (Show, Eq, Ord)

data AnnoType = Declaration | Assertion
    deriving (Show, Eq, Ord)

-- | frames which start with annotations
data AnnFrameBit =
    AnnotationFrameBit AnnoType
  | DataFunctional
  | DatatypeBit DataRange
  | ClassDisjointUnion [ClassExpression]
  | ClassHasKey [ObjectPropertyExpression] [DataPropertyExpression]
  | ObjectSubPropertyChain [ObjectPropertyExpression]
    deriving (Show, Eq, Ord)

data Fact =
    ObjectPropertyFact PositiveOrNegative ObjectPropertyExpression Individual
  | DataPropertyFact PositiveOrNegative DataPropertyExpression Literal
  deriving (Show, Eq, Ord)

data FrameBit =
    ListFrameBit (Maybe Relation) ListFrameBit
  | AnnFrameBit Annotations AnnFrameBit
    deriving (Show, Eq, Ord)

data Frame = Frame Extended [FrameBit]
    deriving (Show, Eq, Ord)

data Axiom = PlainAxiom
  { axiomTopic :: Extended
  , axiomBit :: FrameBit
  } deriving (Show, Eq, Ord)

mkExtendedEntity :: Entity -> Extended
mkExtendedEntity e@(Entity ty iri) = case ty of
  Class -> ClassEntity $ Expression iri
  ObjectProperty -> ObjectEntity $ ObjectProp iri
  _ -> SimpleEntity e

getAxioms :: Frame -> [Axiom]
getAxioms (Frame e fbl) = map (PlainAxiom e) fbl

axToFrame :: Axiom -> Frame
axToFrame (PlainAxiom e fb) = Frame e [fb]

instance GetRange Axiom where
  getRange = Range . joinRanges . map rangeSpan . Set.toList . symsOfAxiom

data Ontology = Ontology
    { name :: OntologyIRI
    , imports :: [ImportIRI]
    , ann :: [Annotations]
    , ontFrames :: [Frame]
    } deriving (Show, Eq, Ord)

data OntologyDocument = OntologyDocument
    { prefixDeclaration :: PrefixMap
    , ontology :: Ontology
    } deriving (Show, Eq, Ord)

instance GetRange OntologyDocument

emptyOntology :: [Frame] -> Ontology
emptyOntology = Ontology nullQName [] []

emptyOntologyDoc :: OntologyDocument
emptyOntologyDoc = OntologyDocument Map.empty $ emptyOntology []

isEmptyOntology :: Ontology -> Bool
isEmptyOntology (Ontology oiri annoList impList fs) = isNullQName oiri
    && null annoList && null impList && null fs

isEmptyOntologyDoc :: OntologyDocument -> Bool
isEmptyOntologyDoc (OntologyDocument ns onto) =
    Map.null ns && isEmptyOntology onto

emptyAnnoList :: [a] -> AnnotatedList a
emptyAnnoList = map $ \ x -> ([], x)

symsOfAxiom :: Axiom -> Set.Set Entity
symsOfAxiom (PlainAxiom e f) = Set.union (symsOfExtended e) $ symsOfFrameBit f

symsOfExtended :: Extended -> Set.Set Entity
symsOfExtended e = case e of
  Misc as -> symsOfAnnotations as
  SimpleEntity s -> Set.singleton s
  ObjectEntity o -> symsOfObjectPropertyExpression o
  ClassEntity c -> symsOfClassExpression c

symsOfObjectPropertyExpression :: ObjectPropertyExpression -> Set.Set Entity
symsOfObjectPropertyExpression o = case o of
  ObjectProp i -> Set.singleton $ Entity ObjectProperty i
  ObjectInverseOf i -> symsOfObjectPropertyExpression i

symsOfClassExpression :: ClassExpression -> Set.Set Entity
symsOfClassExpression ce = case ce of
  Expression c -> Set.singleton $ Entity Class c
  ObjectJunction _ cs -> Set.unions $ map symsOfClassExpression cs
  ObjectComplementOf c -> symsOfClassExpression c
  ObjectOneOf is -> Set.fromList $ map (Entity NamedIndividual) is
  ObjectValuesFrom _ oe c -> Set.union (symsOfObjectPropertyExpression oe)
    $ symsOfClassExpression c
  ObjectHasValue oe i -> Set.insert (Entity NamedIndividual i)
    $ symsOfObjectPropertyExpression oe
  ObjectHasSelf oe -> symsOfObjectPropertyExpression oe
  ObjectCardinality (Cardinality _ _ oe mc) -> Set.union
    (symsOfObjectPropertyExpression oe)
    $ maybe Set.empty symsOfClassExpression mc
  DataValuesFrom _ de dr -> Set.insert (Entity DataProperty de)
    $ symsOfDataRange dr
  DataHasValue de _ -> Set.singleton $ Entity DataProperty de
  DataCardinality (Cardinality _ _ d m) -> Set.insert (Entity DataProperty d)
    $ maybe Set.empty symsOfDataRange m

symsOfDataRange :: DataRange -> Set.Set Entity
symsOfDataRange dr = case dr of
  DataType t _ -> Set.singleton $ Entity Datatype t
  DataJunction _ ds -> Set.unions $ map symsOfDataRange ds
  DataComplementOf d -> symsOfDataRange d
  DataOneOf _ -> Set.empty

symsOfAnnotation :: Annotation -> Set.Set Entity
symsOfAnnotation (Annotation as p _) = Set.insert
   (Entity AnnotationProperty p) $ Set.unions (map symsOfAnnotation as)

symsOfAnnotations :: Annotations -> Set.Set Entity
symsOfAnnotations = Set.unions . map symsOfAnnotation

symsOfFrameBit :: FrameBit -> Set.Set Entity
symsOfFrameBit fb = case fb of
  ListFrameBit _ lb -> symsOfListFrameBit lb
  AnnFrameBit as af -> Set.union (symsOfAnnotations as) $ symsOfAnnFrameBit af

symsOfAnnFrameBit :: AnnFrameBit -> Set.Set Entity
symsOfAnnFrameBit af = case af of
  AnnotationFrameBit _ -> Set.empty
  DataFunctional -> Set.empty
  DatatypeBit dr -> symsOfDataRange dr
  ClassDisjointUnion cs -> Set.unions $ map symsOfClassExpression cs
  ClassHasKey os ds -> Set.union
    (Set.unions $ map symsOfObjectPropertyExpression os)
    . Set.fromList $ map (Entity DataProperty) ds
  ObjectSubPropertyChain os ->
    Set.unions $ map symsOfObjectPropertyExpression os

symsOfListFrameBit :: ListFrameBit -> Set.Set Entity
symsOfListFrameBit lb = case lb of
  AnnotationBit l -> annotedSyms (Set.singleton . Entity AnnotationProperty) l
  ExpressionBit l -> annotedSyms symsOfClassExpression l
  ObjectBit l -> annotedSyms symsOfObjectPropertyExpression l
  DataBit l -> annotedSyms (Set.singleton . Entity DataProperty) l
  IndividualSameOrDifferent l -> annotedSyms
    (Set.singleton . Entity NamedIndividual) l
  ObjectCharacteristics l -> annotedSyms (const Set.empty) l
  DataPropRange l -> annotedSyms symsOfDataRange l
  IndividualFacts l -> annotedSyms symsOfFact l

symsOfFact :: Fact -> Set.Set Entity
symsOfFact fact = case fact of
  ObjectPropertyFact _ oe i -> Set.insert (Entity NamedIndividual i)
    $ symsOfObjectPropertyExpression oe
  DataPropertyFact _ d _ -> Set.singleton $ Entity DataProperty d

annotedSyms :: (a -> Set.Set Entity) -> AnnotatedList a -> Set.Set Entity
annotedSyms f l = Set.union (Set.unions $ map (symsOfAnnotations . fst) l)
  . Set.unions $ map (f . snd) l
