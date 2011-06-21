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

convertFrameBit :: Entity -> FrameBit -> [Axiom]
convertFrameBit (Entity e iri) fb = case fb of
    AnnotationFrameBit ans -> [EntityAnno $ AnnotationAssertion (convertAnnos ans) iri]
    AnnotationBit ed anl ->  map (\ (ans, b) -> EntityAnno $ AnnotationAxiom ed ans iri b) (convertAnnList anl)
    DatatypeBit ans dr -> [PlainAxiom (convertAnnos ans) $ DatatypeDefinition iri dr]
    ExpressionBit ed anl -> map (\ (ans, b) -> ) (convertAnnList anl)

{-
convertClassBit :: IRI -> ClassFrameBit -> [Axiom]
convertClassBit iri fb = let cle = Expression iri in case fb of
    ClassAnnotations x -> [EntityAnno $ AnnotationAssertion (convertAnnos x) iri]
    ClassSubClassOf al -> map (\ (ans, b) -> PlainAxiom ans $ SubClassOf cle b) (convertAnnList al)
    ClassEquivOrDisjoint ed al -> let x = convertAnnList al in [PlainAxiom (concatMap fst x) $ EquivOrDisjointClasses ed (cle : map snd x)] 
    ClassDisjointUnion ans ce -> [PlainAxiom (convertAnnos ans) $ DisjointUnion iri ce]
    ClassHasKey ans opl dpl -> [PlainAxiom (convertAnnos ans) $ HasKey cle opl dpl]

convertObjectBit :: IRI -> ObjectFrameBit -> [Axiom]
convertObjectBit iri ob = let op = ObjectProp iri in case ob of
    ObjectDomainOrRange dr ls -> map (\ (ans, b) -> PlainAxiom ans $ ObjectPropertyDomainOrRange dr op b) (convertAnnList ls)
    ObjectCharacteristics anc -> map (\ (ans, b) -> PlainAxiom ans $ ObjectPropertyCharacter b op) (convertAnnList anc)
    ObjectEquivOrDisjoint ed anl -> let x = convertAnnList anl in [PlainAxiom (concatMap fst x) $ EquivOrDisjointObjectProperties ed (op : map snd x)]
    ObjectInverse anl -> map (\ (ans, b) -> PlainAxiom ans $ InverseObjectProperties op b) (convertAnnList anl)
    ObjectSubPropertyOf anl -> map (\ (ans, b) -> PlainAxiom ans $ SubObjectPropertyOf (OPExpression b) op) (convertAnnList anl)
    ObjectSubPropertyChain ans opl = let x = convertAnnList ans in [PlainAxiom (concatMap fst x) $ SubObjectPropertyOf ()]

= ObjectAnnotations Annotations
  | ObjectDomainOrRange ObjDomainOrRange (AnnotatedList ClassExpression)
  | ObjectCharacteristics (AnnotatedList Character)
  | ObjectEquivOrDisjoint EquivOrDisjoint (AnnotatedList ObjectPropertyExpression)
  | ObjectInverse (AnnotatedList ObjectPropertyExpression)
  | ObjectSubPropertyChain Annotations [ObjectPropertyExpression]
  | ObjectSubPropertyOf (AnnotatedList ObjectPropertyExpression)
-}
