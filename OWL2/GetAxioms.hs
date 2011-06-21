{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  Get the Axioms from the Manchester Syntax frames
-}

module OWL2.GetAxioms where

import OWL2.AS
import OWL2.MS
import OWL2.FS
import Common.Keywords
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
    ExpressionBit ed anl -> let x = convertAnnList anl in 
        case e of
          Class -> case ed of
            SubClass -> map (\ (ans, b) -> PlainAxiom ans $ SubClassOf (Expression iri) b) x   
            _ -> [PlainAxiom (concatMap fst x) $ EquivOrDisjointClasses ed ((Expression iri) : (map snd x) )]
          ObjectProperty -> map (\ (ans, b) -> PlainAxiom ans $ ObjectPropertyDomainOrRange ed (ObjectProp iri) b) x
          DataProperty -> map (\ (ans, b) -> PlainAxiom ans $ DataPropertyDomainOrRange (DataDomain b) iri) x
          NamedIndividual -> map (\ (ans, b) -> PlainAxiom ans $ ClassAssertion b iri) x
    ClassDisjointUnion ans ce -> [PlainAxiom (convertAnnos ans) $ DisjointUnion iri ce]
    ClassHasKey ans opl dpl -> [PlainAxiom (convertAnnos ans) $ HasKey (Expression iri) opl dpl]
    ObjectBit ed anl -> let x = convertAnnList anl in 
        case ed of
          InverseOf -> map (\ (ans, b) -> PlainAxiom ans $ InverseObjectProperties (ObjectProp iri) b) x
          SubPropertyOf -> map (\ (ans, b) -> PlainAxiom ans $ SubObjectPropertyOf (OPExpression b) (ObjectProp iri)) x
          _ -> [PlainAxiom (concatMap fst x) $ EquivOrDisjointObjectProperties ed ((ObjectProp iri) : map snd x)]
    ObjectCharacteristics anc -> map (\ (ans, b) -> PlainAxiom ans $ ObjectPropertyCharacter b (ObjectProp iri)) (convertAnnList anc)
    ObjectSubPropertyChain ans opl -> let x = convertAnnos ans in [PlainAxiom x 
              $ SubObjectPropertyOf (SubObjectPropertyChain opl) (ObjectProp iri)]
    DataBit ed anl -> let x = convertAnnList anl in
        case ed of
          SubPropertyOf -> map (\ (ans, b) -> PlainAxiom ans $ SubDataPropertyOf iri b) x
          _ -> [PlainAxiom (concatMap fst x) $ EquivOrDisjointDataProperties ed (iri : map snd x)]
    DataPropRange anl -> map (\ (ans, b) -> PlainAxiom ans $ DataPropertyDomainOrRange (DataRange b) iri) (convertAnnList anl)
    DataFunctional anl -> [PlainAxiom (convertAnnos anl) $ FunctionalDataProperty iri]
    IndividualFacts anl -> let x = convertAnnList anl in map (\ (ans, b) -> PlainAxiom ans $ (convertFact iri b)) x
    IndividualSameOrDifferent sd anl -> let x = convertAnnList anl in 
        [PlainAxiom (concatMap fst x) $ SameOrDifferentIndividual sd (iri : map snd x)]

convertFact :: Individual -> Fact -> PlainAxiom
convertFact i f = case f of
    ObjectPropertyFact pn ope i2 -> ObjectPropertyAssertion $ Assertion ope pn i i2
    DataPropertyFact pn dpe i2 -> DataPropertyAssertion $ Assertion dpe pn i i2

convertMisc :: Relation -> Annotations -> Misc -> Axiom
convertMisc ed ans misc = let x = convertAnnos ans in case misc of
    MiscEquivOrDisjointClasses l -> PlainAxiom x $ EquivOrDisjointClasses ed l
    MiscEquivOrDisjointObjProp l -> PlainAxiom x $ EquivOrDisjointObjectProperties ed l
    MiscEquivOrDisjointDataProp l -> PlainAxiom x $ EquivOrDisjointDataProperties ed l

getAxioms :: Frame -> [Axiom]
getAxioms f = case f of
    Frame e fbl -> concatMap (convertFrameBit e) fbl
    MiscFrame ed ans misc -> [convertMisc ed ans misc]    
    MiscSameOrDifferent sd ans il -> let x = convertAnnos ans in 
        [PlainAxiom x $ SameOrDifferentIndividual sd il]
