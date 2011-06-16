{-# LANGUAGE DeriveDataTypeable #-}

module OWL2.MS where

import OWL2.AS
import Common.Keywords
import Common.Id (GetRange)

import OWL.Keywords
import OWL.ColonKeywords
import qualified Data.Map as Map
import Data.Typeable

data AnnotatedList a = AnnotatedList [([Annotation], a)]
   deriving (Typeable, Show, Eq, Ord)

data DatatypeFrame = DatatypeFrame Datatype [AnnotatedList Annotation] (Maybe ([Annotation], DataRange))
  deriving (Typeable, Show, Eq, Ord)

data ClassFrame = ClassFrame Class [ClassFrameBit]
  deriving (Typeable, Show, Eq, Ord)

data ClassFrameBit 
  = ClassAnnotations (AnnotatedList Annotation)  -- nonEmpty list
  | ClassSubClassOf (AnnotatedList ClassExpression)   -- nonEmpty list
  | ClassEquivOrDisjoint EquivOrDisjoint (AnnotatedList ClassExpression) --nonEmpty list
  | ClassDisjointUnion [Annotation] [ClassExpression] -- min 2 class expressions
  | ClassHasKey [Annotation] [ObjectPropertyExpression] [DataPropertyExpression]
  deriving (Typeable, Show, Eq, Ord)

data ObjectPropertyFrame = ObjectPropertyFrame ObjectPropertyExpression [ObjectFrameBit]
  deriving (Typeable, Show, Eq, Ord)

data ObjectFrameBit 
  = ObjectAnnotations (AnnotatedList Annotation)
  | ObjectDomainOrRange ObjDomainOrRange (AnnotatedList ClassExpression)
  | ObjectCharacteristics (AnnotatedList Character)
  | ObjectEquivOrDisjoint EquivOrDisjoint (AnnotatedList ObjectPropertyExpression)
  | ObjectInverse (AnnotatedList ObjectPropertyExpression)
  | ObjectSubPropertyChain [Annotation] [ObjectPropertyExpression]
  | ObjectSubPropertyOf (AnnotatedList ObjectPropertyExpression)
  deriving (Typeable, Show, Eq, Ord)

data DataPropertyFrame = DataPropertyFrame DataPropertyExpression [DataFrameBit]
  deriving (Typeable, Show, Eq, Ord)

data DataFrameBit 
  = DataAnnotations (AnnotatedList Annotation)
  | DataPropDomainOrRange (AnnotatedList DataDomainOrRange)
  | DataFunctional [Annotation]
  | DataSubPropertyOf (AnnotatedList DataPropertyExpression)
  | DataEquivOrDisjoint EquivOrDisjoint (AnnotatedList DataPropertyExpression)
  deriving (Typeable, Show, Eq, Ord)

data IndividualFrame = IndividualFrame Individual [IndividualBit]
  deriving (Typeable, Show, Eq, Ord)

data IndividualBit 
  = IndividualAnnotations (AnnotatedList Annotation)
  | IndividualTypes (AnnotatedList ClassExpression)
  | IndividualFacts (AnnotatedList Fact)
  | IndividualSameOrDifferent SameOrDifferent (AnnotatedList Individual)
  deriving (Typeable, Show, Eq, Ord)

data Fact 
  = ObjectPropertyFact (Maybe ()) ObjectPropertyExpression Individual
  | DataPropertyExpression (Maybe ()) DataPropertyExpression Literal
  deriving (Typeable, Show, Eq, Ord)

data AnnotationFrame = AnnotationFrame AnnotationProperty [AnnotationBit]
  deriving (Typeable, Show, Eq, Ord)

data AnnotationBit 
  = AnnotationAnnotations (AnnotatedList Annotation)
  | AnnotationDOR AnnotationDomainOrRange (AnnotatedList IRI)
  | AnnotationSubPropertyOf (AnnotatedList AnnotationProperty)
  deriving (Typeable, Show, Eq, Ord)

data Misc 
  = MiscEquivOrDisjointClasses EquivOrDisjoint [Annotation] [ClassExpression]
  | MiscEquivOrDisjointObjProp EquivOrDisjoint [Annotation] [ObjectPropertyExpression]
  | MiscEquivOrDisjointDataProp EquivOrDisjoint [Annotation] [DataPropertyExpression]
  | MiscSameOrDifferent SameOrDifferent [Annotation] [Individual]
  deriving (Typeable, Show, Eq, Ord)







               


