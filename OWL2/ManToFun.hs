module OWL2.ManToFun where

import OWL2.AS
import OWL2.MS
import OWL2.FS
import OWL2.Parse
import OWL2.ManchesterParser
import Common.Parsec
import Common.Keywords
import Text.ParserCombinators.Parsec
import OWL2.FunctionalPrint
import OWL2.Print
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords

convertAnnos :: Annotations -> [Annotation]
convertAnnos (Annotations l) =
  map (\ (ans, Annotation _ ap av) -> Annotation (convertAnnos ans) ap av) l
 
convertAnnList :: (AnnotatedList a) -> [([Annotation], a)]
convertAnnList (AnnotatedList x) = 
  map (\ (ans, b) -> (convertAnnos ans, b)) x
    
        

convert :: Frame -> [Axiom]
convert f = case f of
    ClassFrame c cfb -> case cfb of 
        [] -> []
        (ClassAnnotations x) : t -> (EntityAnno $ AnnotationAssertion (convertAnnos x) c) : (convert $ ClassFrame c t)
        --(ClassSubClassOf x) : t -> (PlainAxiom $ SubClassOf () c)
        
      
{-
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
-}
