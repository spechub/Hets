{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.
-}

module OWL_DL.AS where

type URIreference = String

type DatatypeID = URIreference
type ClassID = URIreference
type IndividualID = URIreference
type OntologyID = URIreference
type DatavaluedPropertyID = URIreference
type IndividualvaluedPropertyID = URIreference
type AnnotationPropertyID = URIreference
type OntologyPropertyID = URIreference

-- | Data structur for Ontologies
data Ontology = Ontology (Maybe OntologyID) [Directive]
                deriving (Show, Eq)
data Directive = Anno Annotation | Ax Axiom | Fc Fact
                 deriving (Show, Eq)
data Annotation = URIAnnotation 
                         AnnotationPropertyID 
                         URIreference
                | DLAnnotation 
                         AnnotationPropertyID 
                         DataLiteral
                | IndivAnnotation 
                         AnnotationPropertyID 
                         Individual
                  deriving (Show, Eq)

-- | Data literal
data DataLiteral = TypedL TypedLiteral 
                 | PlainL PlainLiteral
                   deriving (Show, Eq)
type TypedLiteral = (LexicalForm, URIreference)  
                    -- ^ consist of a lexical representatoin and a URI.                   
type PlainLiteral = (LexicalForm, LanguageTag)  
                    -- ^ Unicode string in Normal Form C and an optional language tag
type LexicalForm = String        
type LanguageTag = String

-- | Data structur for facts
data Fact = Indiv Individual 
          | SameIndividual 
                  IndividualID 
                  IndividualID 
                  [IndividualID]
          | DifferentIndividuals 
                  IndividualID 
                  IndividualID 
                  [IndividualID]
            deriving (Show, Eq)

data Individual = Individual (Maybe IndividualID) [Annotation] (Maybe Type) (Maybe Value)
                  deriving (Show, Eq)
data Value = ValueID    IndividualvaluedPropertyID IndividualID
           | ValueIndiv IndividualvaluedPropertyID Individual
           | ValueDL    DatavaluedPropertyID DataLiteral
             deriving (Show, Eq)
type Type = Description

-- | Axiom (Class Axioms, Descriptions, Restrictions, Property Axioms)
data Axiom = Class 
                   ClassID 
                   Bool -- ^ True == deprecated
                   Modality 
                   [Annotation] 
                   [Description]
           | EnumeratedClass 
                   ClassID 
                   Bool -- ^ True == deprecated
                   [Annotation] 
                   [IndividualID]
           | DisjointClasses 
                   Description 
                   Description 
                   [Description]
           | EquivalentClasses 
                   Description 
                   [Description]
           | SubClassOf 
                   Description 
                   Description
           | Datatype 
                   DatatypeID 
                   Bool -- ^ True == deprecated  
                   [Annotation]
           | DatatypeProperty 
                   DatavaluedPropertyID 
                   Bool -- ^ True == deprecated  
                   [Annotation] 
                   [DatavaluedPropertyID]  -- ^ super properties 
                   (Maybe Func) 
                   [Description] -- ^ Domain 
                   [DataRange] -- ^ Range
           | ObjectProperty IndividualvaluedPropertyID 
                   Bool -- ^ True == deprecated 
                   [Annotation] 
                   [IndividualvaluedPropertyID] -- ^ super properties 
                   (Maybe IndividualvaluedPropertyID)
                      -- ^ inverse of property 
                   Bool -- ^ True == symmetric
                   (Maybe Func) 
                   [Description] -- ^ Domain 
                   [Description] -- ^ Range
           | AnnotaionProperty 
                   AnnotationPropertyID 
                   [Annotation]
           | OntologyProperty 
                   OntologyPropertyID 
                   [Annotation]
           | DEquivalentProperties 
                   DatavaluedPropertyID 
                   DatavaluedPropertyID 
                   [DatavaluedPropertyID]
           | DSubPropertyOf 
                   DatavaluedPropertyID 
                   DatavaluedPropertyID
           | IEquivalentProperty 
                   IndividualvaluedPropertyID 
                   IndividualvaluedPropertyID 
                   [IndividualvaluedPropertyID]
           | ISubPropertyOf 
                   IndividualvaluedPropertyID 
                   IndividualvaluedPropertyID
             deriving (Show, Eq)

data Func = Functional | InverseFunctional | Functional_InverseFunctional | Transitive
            deriving (Show, Eq)

data Modality = Complete | Partial
                deriving (Show, Eq)
data Description = DC ClassID 
                 | DR Restriction
                 | UnionOf [Description]
                 | IntersectionOf [Description]
                 | ComplementOf Description
                 | OneOfDes [IndividualID]
                   deriving (Show, Eq)

data Restriction = DataRestriction DatavaluedPropertyID Drcomponent [Drcomponent]
                 | IndivRestriction IndividualvaluedPropertyID Ircomponent [Ircomponent]
                   deriving (Show, Eq)

data Drcomponent = DRCAllValuesFrom Description
                 | DRCSomeValuesFrom DataRange
                 | DRCValue DataLiteral
                 | DRCCardinatlity Cardinality
                   deriving (Show, Eq)
                   
data Ircomponent = IRCAllValuesFrom Description
                 | IRCSomeValuesFrom Description
                 | IRCValue IndividualID
                 | IRCCardinatlity Cardinality
                   deriving (Show, Eq)

data Cardinality = MinCardinality Int
                 | MaxCardinality Int
                 | Cardinality Int
                   deriving (Show, Eq)

data DataRange = DID DatatypeID 
               | OneOfData [DataLiteral]
               | RL DataLiteral       -- ^ rdfs:literal
                 deriving (Show, Eq)

