module OWL_DL.AS where

type URIreference = String

-- Data structur for Ontologies
type DatatypeID = URIreference
type ClassID = URIreference
type IndividualID = URIreference
type OntologyID = URIreference
type DatavaluedPropertyID = URIreference
type IndividualvaluedPropertyID = URIreference
type AnnotationPropertyID = URIreference
type OntologyPropertyID = URIreference

data Ontology = Ontology (Maybe OntologyID) [Directive]
                deriving (Show, Eq)
data Directive = Anno Annotation | Ax Axiom | Fc Fact
                 deriving (Show, Eq)
data Annotation = URIAnnotation AnnotationPropertyID URIreference
                | DLAnnotation AnnotationPropertyID DataLiteral
                | IndivAnnotation AnnotationPropertyID Individual
                  deriving (Show, Eq)

-- Data structur for facts
data DataLiteral = TypedL TypedLiteral | PlainL PlainLiteral
                   deriving (Show, Eq)
type TypedLiteral = (LexicalForm, URIreference) -- consist of a lexical representatoin and a URI.
                   
type PlainLiteral =  -- Unicode string in Normal Form C and an optional language tag
                    (LexicalForm, LanguageTag)  

type LexicalForm = String        
type LanguageTag = String      -- XMLLT?? an XML language tag

data Fact = Indiv Individual 
          | SameIndividual IndividualID IndividualID [IndividualID]
          | DifferentIndividuals IndividualID IndividualID [IndividualID]
            deriving (Show, Eq)
data Individual = Individual (Maybe IndividualID) [Annotation] (Maybe Type) (Maybe Value)
                  deriving (Show, Eq)
data Value = ValueID    IndividualvaluedPropertyID IndividualID
           | ValueIndiv IndividualvaluedPropertyID Individual
           | ValueDL    DatavaluedPropertyID DataLiteral
             deriving (Show, Eq)
type Type = Restriction

-- Axiom (Class Axioms, Descriptions, Restrictions, Property Axioms)
data Axiom = Class ClassID (Maybe Deprecated) Modality [Annotation] [Description]
           | EnumeratedClass ClassID (Maybe Deprecated) [Annotation] [IndividualID]
           | DisjointClasses Description Description [Description]
           | EquivalentClasses Description [Description]
           | SubClassOf Description Description
           | Datatype DatatypeID (Maybe Deprecated) [Annotation]
           | DatatypeProperty DatavaluedPropertyID (Maybe Deprecated) [Annotation] [Super DatavaluedPropertyID] (Maybe Func) [Domain Description] [Range DataRange]          -- ??
           | ObjectProperty IndividualvaluedPropertyID (Maybe Deprecated) [Annotation] [Super IndividualvaluedPropertyID] (Maybe IndividualvaluedPropertyID) (Maybe Symm) (Maybe Func) [Domain Description] [Range Description]
           | AnnotationProperty AnnotationPropertyID [Annotation]
           | OntologyProperty OntologyPropertyID [Annotation]
           | DEquivalentProperties DatavaluedPropertyID DatavaluedPropertyID [DatavaluedPropertyID]
           | DSubPropertyOf DatavaluedPropertyID DatavaluedPropertyID
           | IEquivalentProperty IndividualvaluedPropertyID IndividualvaluedPropertyID [IndividualvaluedPropertyID]
           | ISubPropertyOf IndividualvaluedPropertyID IndividualvaluedPropertyID
             deriving (Show, Eq)

data Func = Functional | InverseFunctional | Functional_InverseFunctional | Transitive
            deriving (Show, Eq)
data Deprecated = Deprecated  
                  deriving (Show, Eq)
data Symm =  Symmetric  
             deriving (Show, Eq)
data Super a = Super a  deriving (Show, Eq)
data Domain a = Domain a deriving (Show, Eq)
data Range a = Range a deriving (Show, Eq)

data Modality = Complete | Partial
                deriving (Show, Eq)
data Description = DC ClassID 
                 | DR Restriction
                 | UnionOf [Description]
                 | IntersectionOf [Description]
                 | ComplementOf Description
                 | OneOfDes [Description]
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
               | Rdfs_Literal       ------- ????
                 deriving (Show, Eq)