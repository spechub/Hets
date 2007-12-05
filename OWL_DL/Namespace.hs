{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for Namespace and Named Sentence)

This module implements a namespace transformation
-}

module OWL.Namespace where

import qualified OWL.Sign as OS11
import qualified OWL.AS as AS
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.AS_Annotation as Common.Annotation
import Data.List(find, nub)
import Data.Maybe(fromJust)
import Data.Char(isDigit, isAlpha)

type TranslationMap = Map.Map String String  -- ^ OldPrefix -> NewPrefix

-- | propagate own namespaces from prefix to namespacesURI within a ontology
class PNamespace a where
    -- | separate localpart of a QName into two divide: prefix and new
    -- | localpart. If uri of the QName already existed in NamespaceMap,
    -- | should prefix also be changed.
    propagateNspaces :: Namespace -> a -> a
    -- | on the basis of translation map changes the prefix of namespace.
    renameNamespace :: TranslationMap -> a -> a

instance PNamespace Namespace where
    propagateNspaces _ ns = ns
    renameNamespace tMap oldNs =
        trans tMap (Map.toList oldNs) Map.empty
        where trans :: TranslationMap -> [(String, String)]
                    -> Namespace -> Namespace
              trans _ [] ns = ns
              trans tm ((pre, uri):rest) ns =
                  case Map.lookup pre tm of
                  Just pre' -> trans tm rest (Map.insert pre' uri ns)
                  _         -> trans tm rest (Map.insert pre uri ns)

instance PNamespace QName where
    propagateNspaces ns old@(QN pre local nsUri) =
     if local == "Thing" || (snd $ span (/=':') local) == ":Thing" then
        QN "owl" "Thing" "http://www.w3.org/2002/07/owl#"
      else
        if null nsUri then
           if null pre then
              let (pre', local') = span (/=':')
                                     (if (head local) == '\"' then
                                         read local::String
                                         else local
                                     )
              -- hiding "ftp://" oder "http://"
              in if ((length pre' > 3) && (isAlpha $ head $ reverse pre'))
                     || (null local') then
                    QN pre local nsUri
                    else let local'' = tail local'
                         in  prop pre' local''
              else prop pre local
           else
             if null pre then
                case Map.lookup (nsUri ++ "#") (reverseMap ns) of
                  Prelude.Nothing -> old
                  -- if uri of QName already existed in namespace map, must
                  -- the prefix also changed (as is located in map).
                  Just pre' -> QN pre' local nsUri
                else old
      where
        prop :: String -> String -> QName
        prop p loc =
           let maybeNsUri = Map.lookup p ns
           in  case maybeNsUri of
                    Just nsURI -> QN p loc nsURI
                    Prelude.Nothing    -> QN p loc ""

    renameNamespace tMap old@(QN pre local nsUri) =
        case Map.lookup pre tMap of
        Prelude.Nothing -> old
        Just pre' -> QN pre' local nsUri

instance PNamespace OS11.Sign where
   propagateNspaces _ sig = sig

   renameNamespace tMap (OS11.Sign p1 p2 p3 p4 p5 p6 p7 p8 p9 p10) =
       OS11.Sign (renameNamespace tMap p1)
            (Set.map (renameNamespace tMap) p2)
            (Set.map (renameNamespace tMap) p3)
            (Set.map (renameNamespace tMap) p4)
            (Set.map (renameNamespace tMap) p5)
            (Set.map (renameNamespace tMap) p6)
            (Set.map (renameNamespace tMap) p7)
            (Set.map (renameNamespace tMap) p8)
            (Set.map (renameNamespace tMap) p9)
            (renameNamespace tMap p10)

instance PNamespace OS11.SignAxiom where
   propagateNspaces _ signAxiom = signAxiom

   renameNamespace tMap signAxiom =
       case signAxiom of
       OS11.Subconcept cId1 cId2 ->
           OS11.Subconcept (renameNamespace tMap cId1)
                   (renameNamespace tMap cId2)
       OS11.RoleDomain id1 rDomains ->
           OS11.RoleDomain (renameNamespace tMap id1)
                   (renameNamespace tMap rDomains)
       OS11.RoleRange id1 rRange ->
           OS11.RoleRange (renameNamespace tMap id1)
                   (renameNamespace tMap rRange)
       OS11.FuncRole (t, id1) ->
           OS11.FuncRole (t, (renameNamespace tMap id1))
       OS11.Conceptmembership iId des ->
           OS11.Conceptmembership (renameNamespace tMap iId)
                             (renameNamespace tMap des)
       OS11.DataDomain dpExp domain ->
           OS11.DataDomain (renameNamespace tMap dpExp)
                      (renameNamespace tMap domain)
       OS11.DataRange dpExp range ->
           OS11.DataRange (renameNamespace tMap dpExp)
                      (renameNamespace tMap range)
       OS11.FuncDataProp dpExp ->
           OS11.FuncDataProp (renameNamespace tMap dpExp)
       OS11.RefRole (t, opExp) ->
           OS11.RefRole (t, (renameNamespace tMap opExp))


instance PNamespace OS11.RDomain where
    propagateNspaces _ rd = rd
    renameNamespace tMap rd =
        case rd of
        OS11.RDomain des -> OS11.RDomain (renameNamespace tMap des)
        OS11.DDomain des -> OS11.DDomain (renameNamespace tMap des)

instance PNamespace OS11.Sentence where
   propagateNspaces _ sent = sent

   renameNamespace tMap sent =
       case sent of
       OS11.OWLAxiom axiom -> OS11.OWLAxiom (renameNamespace tMap axiom)
       OS11.OWLFact fact   -> OS11.OWLFact  (renameNamespace tMap fact)

instance PNamespace (Common.Annotation.Named Sentence) where
    propagateNspaces _ nsent = nsent

    renameNamespace tMap sent = sent {
        Common.Annotation.sentence = renameNamespace tMap
                                     (Common.Annotation.sentence sent) }

instance PNamespace (Common.Annotation.Named OS11.Sentence) where
    propagateNspaces _ nsent = nsent

    renameNamespace tMap sent = sent {
        Common.Annotation.sentence = renameNamespace tMap
                                     (Common.Annotation.sentence sent) }

instance PNamespace AS.OntologyFile where
    propagateNspaces ns (AS.OntologyFile namespace ontology) =
        AS.OntologyFile (propagateNspaces ns namespace)
                         (propagateNspaces ns ontology)
    renameNamespace tMap (AS.OntologyFile namespace ontology) =
        AS.OntologyFile (renameNamespace tMap namespace)
                         (renameNamespace tMap ontology)

instance PNamespace AS.Ontology where
    propagateNspaces ns (AS.Ontology uri importsList annosList axiomsList) =
        AS.Ontology (propagateNspaces ns uri)
                     (map (propagateNspaces ns) importsList)
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) axiomsList)
    renameNamespace tMap (AS.Ontology uri importsList annosList axiomsList) =
        AS.Ontology (renameNamespace tMap uri)
                     (map (renameNamespace tMap) importsList)
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) axiomsList)

instance PNamespace AS.Annotation where
    propagateNspaces ns anno =
        case anno of
          AS.ExplicitAnnotation annoUri constant ->
              AS.ExplicitAnnotation (propagateNspaces ns annoUri)
                                     (propagateNspaces ns constant)
          AS.Label constant ->
              AS.Label (propagateNspaces ns constant)
          AS.Comment constant ->
              AS.Comment (propagateNspaces ns constant)
          AS.Annotation annoUri entity ->
              AS.Annotation (propagateNspaces ns annoUri)
                             (propagateNspaces ns entity)
    renameNamespace tMap anno =
        case anno of
          AS.ExplicitAnnotation annoUri constant ->
              AS.ExplicitAnnotation (renameNamespace tMap annoUri)
                                     (renameNamespace tMap constant)
          AS.Label constant ->
              AS.Label (renameNamespace tMap constant)
          AS.Comment constant ->
              AS.Comment (renameNamespace tMap constant)
          AS.Annotation annoUri entity ->
              AS.Annotation (renameNamespace tMap annoUri)
                             (renameNamespace tMap entity)


instance PNamespace AS.Axiom where
    propagateNspaces ns axiom =
        case axiom of
          AS.SubClassOf annosList sub sup ->
              AS.SubClassOf (map (propagateNspaces ns) annosList)
                             (propagateNspaces ns sub)
                             (propagateNspaces ns sup)
          AS.EquivalentClasses annosList descList ->
              AS.EquivalentClasses (map (propagateNspaces ns) annosList)
                                    (map (propagateNspaces ns) descList)
          AS.DisjointClasses annosList descList ->
              AS.DisjointClasses (map (propagateNspaces ns) annosList)
                                  (map (propagateNspaces ns) descList)
          AS.DisjointUnion annosList classUri descList ->
              AS.DisjointUnion (map (propagateNspaces ns) annosList)
                                (propagateNspaces ns classUri)
                                (map (propagateNspaces ns) descList)
          AS.SubObjectPropertyOf annosList subExp objExp ->
              AS.SubObjectPropertyOf (map (propagateNspaces ns) annosList)
                                      (propagateNspaces ns subExp)
                                      (propagateNspaces ns objExp)
          AS.EquivalentObjectProperties annosList objExpList ->
              AS.EquivalentObjectProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) objExpList)
          AS.DisjointObjectProperties annosList objExpList ->
              AS.DisjointObjectProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) objExpList)
          AS.ObjectPropertyDomain annosList objExp desc ->
              AS.ObjectPropertyDomain (map (propagateNspaces ns) annosList)
                                       (propagateNspaces ns objExp)
                                       (propagateNspaces ns desc)
          AS.ObjectPropertyRange annosList objExp desc ->
              AS.ObjectPropertyRange (map (propagateNspaces ns) annosList)
                                      (propagateNspaces ns objExp)
                                      (propagateNspaces ns desc)
          AS.InverseObjectProperties annosList objExp1 objExp2 ->
              AS.InverseObjectProperties (map (propagateNspaces ns) annosList)
                                          (propagateNspaces ns objExp1)
                                          (propagateNspaces ns objExp2)
          AS.FunctionalObjectProperty annosList objExp ->
              AS.FunctionalObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          AS.InverseFunctionalObjectProperty annosList objExp ->
              AS.InverseFunctionalObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          AS.ReflexiveObjectProperty annosList objExp ->
              AS.ReflexiveObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          AS.IrreflexiveObjectProperty annosList objExp ->
              AS.IrreflexiveObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          AS.SymmetricObjectProperty  annosList objExp ->
              AS.SymmetricObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          AS.AntisymmetricObjectProperty  annosList objExp ->
              AS.AntisymmetricObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          AS.TransitiveObjectProperty annosList objExp ->
              AS.TransitiveObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          AS.SubDataPropertyOf annosList dpExp1 dpExp2 ->
              AS.SubDataPropertyOf (map (propagateNspaces ns) annosList)
                                    (propagateNspaces ns dpExp1)
                                    (propagateNspaces ns dpExp2)
          AS.EquivalentDataProperties annosList dpExpList ->
              AS.EquivalentDataProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) dpExpList)
          AS.DisjointDataProperties annosList  dpExpList ->
              AS.DisjointDataProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) dpExpList)
          AS.DataPropertyDomain annosList dpExp desc ->
              AS.DataPropertyDomain (map (propagateNspaces ns) annosList)
                                     (propagateNspaces ns dpExp)
                                     (propagateNspaces ns desc)
          AS.DataPropertyRange annosList dpExp dataRange ->
              AS.DataPropertyRange (map (propagateNspaces ns) annosList)
                                     (propagateNspaces ns dpExp)
                                     (propagateNspaces ns dataRange)
          AS.FunctionalDataProperty annosList dpExp ->
              AS.FunctionalDataProperty (map (propagateNspaces ns) annosList)
                                         (propagateNspaces ns dpExp)
          AS.SameIndividual annosList indUriList ->
              AS.SameIndividual (map (propagateNspaces ns) annosList)
                                 (map (propagateNspaces ns) indUriList)
          AS.DifferentIndividuals annosList indUriList ->
              AS.DifferentIndividuals  (map (propagateNspaces ns) annosList)
                                        (map (propagateNspaces ns) indUriList)
          AS.ClassAssertion annosList indUri desc ->
              AS.ClassAssertion (map (propagateNspaces ns) annosList)
                                 (propagateNspaces ns indUri)
                                 (propagateNspaces ns desc)
          AS.ObjectPropertyAssertion annosList objExp source target ->
             AS.ObjectPropertyAssertion (map (propagateNspaces ns) annosList)
                                         (propagateNspaces ns objExp)
                                         (propagateNspaces ns source)
                                         (propagateNspaces ns target)
          AS.NegativeObjectPropertyAssertion annosList objExp source target ->
             AS.NegativeObjectPropertyAssertion
                    (map (propagateNspaces ns) annosList)
                    (propagateNspaces ns objExp)
                    (propagateNspaces ns source)
                    (propagateNspaces ns target)
          AS.DataPropertyAssertion annosList dpExp source target ->
              AS.DataPropertyAssertion
                 (map (propagateNspaces ns) annosList)
                 (propagateNspaces ns dpExp)
                 (propagateNspaces ns source)
                 (propagateNspaces ns target)
          AS.NegativeDataPropertyAssertion annosList dpExp source target ->
              AS.NegativeDataPropertyAssertion
                 (map (propagateNspaces ns) annosList)
                 (propagateNspaces ns dpExp)
                 (propagateNspaces ns source)
                 (propagateNspaces ns target)
          AS.Declaration annosList entity ->
              AS.Declaration (map (propagateNspaces ns) annosList)
                              (propagateNspaces ns entity)
          AS.EntityAnno entityAnnotation  ->
              AS.EntityAnno (propagateNspaces ns entityAnnotation)

    renameNamespace tMap axiom =
        case axiom of
          AS.SubClassOf annosList sub sup ->
              AS.SubClassOf (map (renameNamespace tMap) annosList)
                             (renameNamespace tMap sub)
                             (renameNamespace tMap sup)
          AS.EquivalentClasses annosList descList ->
              AS.EquivalentClasses (map (renameNamespace tMap) annosList)
                                    (map (renameNamespace tMap) descList)
          AS.DisjointClasses annosList descList ->
              AS.DisjointClasses (map (renameNamespace tMap) annosList)
                                  (map (renameNamespace tMap) descList)
          AS.DisjointUnion annosList classUri descList ->
              AS.DisjointUnion (map (renameNamespace tMap) annosList)
                                (renameNamespace tMap classUri)
                                (map (renameNamespace tMap) descList)
          AS.SubObjectPropertyOf annosList subExp objExp ->
              AS.SubObjectPropertyOf (map (renameNamespace tMap) annosList)
                                      (renameNamespace tMap subExp)
                                      (renameNamespace tMap objExp)
          AS.EquivalentObjectProperties annosList objExpList ->
              AS.EquivalentObjectProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) objExpList)
          AS.DisjointObjectProperties annosList objExpList ->
              AS.DisjointObjectProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) objExpList)
          AS.ObjectPropertyDomain annosList objExp desc ->
              AS.ObjectPropertyDomain (map (renameNamespace tMap) annosList)
                                       (renameNamespace tMap objExp)
                                       (renameNamespace tMap desc)
          AS.ObjectPropertyRange annosList objExp desc ->
              AS.ObjectPropertyRange (map (renameNamespace tMap) annosList)
                                      (renameNamespace tMap objExp)
                                      (renameNamespace tMap desc)
          AS.InverseObjectProperties annosList objExp1 objExp2 ->
              AS.InverseObjectProperties
                     (map (renameNamespace tMap) annosList)
                     (renameNamespace tMap objExp1)
                     (renameNamespace tMap objExp2)
          AS.FunctionalObjectProperty annosList objExp ->
              AS.FunctionalObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          AS.InverseFunctionalObjectProperty annosList objExp ->
              AS.InverseFunctionalObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          AS.ReflexiveObjectProperty annosList objExp ->
              AS.ReflexiveObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          AS.IrreflexiveObjectProperty annosList objExp ->
              AS.IrreflexiveObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          AS.SymmetricObjectProperty  annosList objExp ->
              AS.SymmetricObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          AS.AntisymmetricObjectProperty  annosList objExp ->
              AS.AntisymmetricObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          AS.TransitiveObjectProperty annosList objExp ->
              AS.TransitiveObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          AS.SubDataPropertyOf annosList dpExp1 dpExp2 ->
              AS.SubDataPropertyOf (map (renameNamespace tMap) annosList)
                                    (renameNamespace tMap dpExp1)
                                    (renameNamespace tMap dpExp2)
          AS.EquivalentDataProperties annosList dpExpList ->
              AS.EquivalentDataProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) dpExpList)
          AS.DisjointDataProperties annosList  dpExpList ->
              AS.DisjointDataProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) dpExpList)
          AS.DataPropertyDomain annosList dpExp desc ->
              AS.DataPropertyDomain (map (renameNamespace tMap) annosList)
                                     (renameNamespace tMap dpExp)
                                     (renameNamespace tMap desc)
          AS.DataPropertyRange annosList dpExp dataRange ->
              AS.DataPropertyRange (map (renameNamespace tMap) annosList)
                                     (renameNamespace tMap dpExp)
                                     (renameNamespace tMap dataRange)
          AS.FunctionalDataProperty annosList dpExp ->
              AS.FunctionalDataProperty (map (renameNamespace tMap) annosList)
                                         (renameNamespace tMap dpExp)
          AS.SameIndividual annosList indUriList ->
              AS.SameIndividual (map (renameNamespace tMap) annosList)
                                 (map (renameNamespace tMap) indUriList)
          AS.DifferentIndividuals annosList indUriList ->
              AS.DifferentIndividuals  (map (renameNamespace tMap) annosList)
                                        (map (renameNamespace tMap) indUriList)
          AS.ClassAssertion annosList indUri desc ->
              AS.ClassAssertion (map (renameNamespace tMap) annosList)
                                 (renameNamespace tMap indUri)
                                 (renameNamespace tMap desc)
          AS.ObjectPropertyAssertion annosList objExp source target ->
             AS.ObjectPropertyAssertion (map (renameNamespace tMap) annosList)
                                         (renameNamespace tMap objExp)
                                         (renameNamespace tMap source)
                                         (renameNamespace tMap target)
          AS.NegativeObjectPropertyAssertion annosList objExp source target ->
             AS.NegativeObjectPropertyAssertion
                    (map (renameNamespace tMap) annosList)
                    (renameNamespace tMap objExp)
                    (renameNamespace tMap source)
                    (renameNamespace tMap target)
          AS.DataPropertyAssertion annosList dpExp source target ->
              AS.DataPropertyAssertion
                 (map (renameNamespace tMap) annosList)
                 (renameNamespace tMap dpExp)
                 (renameNamespace tMap source)
                 (renameNamespace tMap target)
          AS.NegativeDataPropertyAssertion annosList dpExp source target ->
              AS.NegativeDataPropertyAssertion
                 (map (renameNamespace tMap) annosList)
                 (renameNamespace tMap dpExp)
                 (renameNamespace tMap source)
                 (renameNamespace tMap target)
          AS.Declaration annosList entity ->
              AS.Declaration (map (renameNamespace tMap) annosList)
                              (renameNamespace tMap entity)
          AS.EntityAnno entityAnnotation  ->
              AS.EntityAnno (renameNamespace tMap entityAnnotation)

instance PNamespace AS.Entity where
    propagateNspaces ns entity =
        case entity of
          AS.Datatype uri ->
              AS.Datatype (propagateNspaces ns uri)
          AS.OWLClassEntity uri ->
              AS.OWLClassEntity (propagateNspaces ns uri)
          AS.ObjectProperty uri ->
              AS.ObjectProperty (propagateNspaces ns uri)
          AS.DataProperty uri ->
              AS.DataProperty (propagateNspaces ns uri)
          AS.Individual uri ->
              AS.Individual (propagateNspaces ns uri)
    renameNamespace tMap entity =
        case entity of
          AS.Datatype uri ->
              AS.Datatype (renameNamespace tMap uri)
          AS.OWLClassEntity uri ->
              AS.OWLClassEntity (renameNamespace tMap uri)
          AS.ObjectProperty uri ->
              AS.ObjectProperty (renameNamespace tMap uri)
          AS.DataProperty uri ->
              AS.DataProperty (renameNamespace tMap uri)
          AS.Individual uri ->
              AS.Individual (renameNamespace tMap uri)

instance PNamespace AS.Constant where
    propagateNspaces ns constant =
        case constant of
          AS.TypedConstant (l, uri) ->
              AS.TypedConstant (l, (propagateNspaces ns uri))
          u -> u        -- for untyped constant
    renameNamespace tMap constant =
        case constant of
          AS.TypedConstant (l, uri) ->
              AS.TypedConstant (l, (renameNamespace tMap uri))
          u -> u        -- for untyped constant

instance PNamespace AS.ObjectPropertyExpression where
    propagateNspaces ns opExp =
        case opExp of
          AS.OpURI uri -> AS.OpURI (propagateNspaces ns uri)
          AS.InverseOp invOp -> AS.InverseOp (propagateNspaces ns invOp)
    renameNamespace tMap opExp =
        case opExp of
          AS.OpURI uri -> AS.OpURI (renameNamespace tMap uri)
          AS.InverseOp invOp -> AS.InverseOp (renameNamespace tMap invOp)

instance PNamespace AS.DataRange where
    propagateNspaces ns dr =
        case dr of
          AS.DRDatatype uri ->
              AS.DRDatatype (propagateNspaces ns uri)
          AS.DataComplementOf dataRange ->
              AS.DataComplementOf (propagateNspaces ns dataRange)
          AS.DataOneOf constList ->
              AS.DataOneOf (map (propagateNspaces ns) constList)
          AS.DatatypeRestriction dataRange restrList ->
              AS.DatatypeRestriction (propagateNspaces ns dataRange)
                                      (map pnRest restrList)
     where pnRest (facet, value) =
               (facet, propagateNspaces ns value)
    renameNamespace tMap dr =
        case dr of
          AS.DRDatatype uri ->
              AS.DRDatatype (renameNamespace tMap uri)
          AS.DataComplementOf dataRange ->
              AS.DataComplementOf (renameNamespace tMap dataRange)
          AS.DataOneOf constList ->
              AS.DataOneOf (map (renameNamespace tMap) constList)
          AS.DatatypeRestriction dataRange restrList ->
              AS.DatatypeRestriction (renameNamespace tMap dataRange)
                                      (map rnRest restrList)
     where rnRest (facet, value) =
               (facet, renameNamespace tMap value)

instance PNamespace AS.Description where
    propagateNspaces ns desc =
        case desc of
          AS.OWLClass uri ->
              AS.OWLClass (propagateNspaces ns uri)
          AS.ObjectUnionOf descList ->
              AS.ObjectUnionOf (map (propagateNspaces ns) descList)
          AS.ObjectIntersectionOf descList ->
              AS.ObjectIntersectionOf (map (propagateNspaces ns) descList)
          AS.ObjectComplementOf desc' ->
              AS.ObjectComplementOf  (propagateNspaces ns desc')
          AS.ObjectOneOf indsList ->
              AS.ObjectOneOf (map (propagateNspaces ns) indsList)
          AS.ObjectAllValuesFrom opExp desc' ->
              AS.ObjectAllValuesFrom (propagateNspaces ns opExp)
                                      (propagateNspaces ns desc')
          AS.ObjectSomeValuesFrom opExp desc' ->
              AS.ObjectSomeValuesFrom (propagateNspaces ns opExp)
                                       (propagateNspaces ns desc')
          AS.ObjectExistsSelf opExp ->
              AS.ObjectExistsSelf (propagateNspaces ns opExp)
          AS.ObjectHasValue opExp indUri ->
              AS.ObjectHasValue (propagateNspaces ns opExp)
                                 (propagateNspaces ns indUri)
          AS.ObjectMinCardinality card opExp maybeDesc ->
              AS.ObjectMinCardinality card (propagateNspaces ns opExp)
                                       (maybePropagate ns maybeDesc)
          AS.ObjectMaxCardinality card opExp maybeDesc ->
              AS.ObjectMaxCardinality card (propagateNspaces ns opExp)
                                       (maybePropagate ns maybeDesc)
          AS.ObjectExactCardinality card opExp maybeDesc ->
              AS.ObjectExactCardinality card (propagateNspaces ns opExp)
                                         (maybePropagate ns maybeDesc)
          AS.DataAllValuesFrom dpExp dpExpList dataRange ->
              AS.DataAllValuesFrom (propagateNspaces ns dpExp)
                                    (map (propagateNspaces ns) dpExpList)
                                    (propagateNspaces ns dataRange)
          AS.DataSomeValuesFrom dpExp dpExpList dataRange ->
              AS.DataSomeValuesFrom  (propagateNspaces ns dpExp)
                                      (map (propagateNspaces ns) dpExpList)
                                      (propagateNspaces ns dataRange)
          AS.DataHasValue dpExp const' ->
              AS.DataHasValue (propagateNspaces ns dpExp)
                               (propagateNspaces ns const')
          AS.DataMinCardinality  card dpExp maybeRange ->
              AS.DataMinCardinality card (propagateNspaces ns dpExp)
                                     (maybePropagate ns maybeRange)
          AS.DataMaxCardinality card dpExp maybeRange ->
              AS.DataMaxCardinality  card (propagateNspaces ns dpExp)
                                     (maybePropagate ns maybeRange)
          AS.DataExactCardinality card dpExp maybeRange ->
              AS.DataExactCardinality card (propagateNspaces ns dpExp)
                                       (maybePropagate ns maybeRange)

    renameNamespace tMap desc =
        case desc of
          AS.OWLClass uri ->
              AS.OWLClass (renameNamespace tMap uri)
          AS.ObjectUnionOf descList ->
              AS.ObjectUnionOf (map (renameNamespace tMap) descList)
          AS.ObjectIntersectionOf descList ->
              AS.ObjectIntersectionOf (map (renameNamespace tMap) descList)
          AS.ObjectComplementOf desc' ->integrateOntology :: Ontology -> Ontology -> Ontology
integrateOntology onto1@(Ontology oid1 directives1 ns1)
                  onto2@(Ontology oid2 directives2 ns2) =
  if onto1 == onto2 then onto1
   else
    let (newNamespace, transMap) = integrateNamespaces ns1 ns2
    in  Ontology (newOid oid1 oid2)
                 (nub (directives1 ++
                       (map (renameNamespace transMap) directives2)))
                 newNamespace
    where newOid :: Maybe OntologyID -> Maybe OntologyID -> Maybe OntologyID
          newOid Prelude.Nothing Prelude.Nothing = Prelude.Nothing
          newOid Prelude.Nothing oid@(Just _) = oid
          newOid oid@(Just _) Prelude.Nothing = oid
          newOid (Just id1) (Just id2) =
              if id1 == id2 then Just id1
                 else
                 Just (id1 { localPart=
                             (uriToName $ localPart id1) ++
                             "_" ++
                             (uriToName $ uriToName $ localPart id2)})


              AS.ObjectComplementOf  (renameNamespace tMap desc')
          AS.ObjectOneOf indsList ->
              AS.ObjectOneOf (map (renameNamespace tMap) indsList)
          AS.ObjectAllValuesFrom opExp desc' ->
              AS.ObjectAllValuesFrom (renameNamespace tMap opExp)
                                      (renameNamespace tMap desc')
          AS.ObjectSomeValuesFrom opExp desc' ->
              AS.ObjectSomeValuesFrom (renameNamespace tMap opExp)
                                       (renameNamespace tMap desc')
          AS.ObjectExistsSelf opExp ->
              AS.ObjectExistsSelf (renameNamespace tMap opExp)
          AS.ObjectHasValue opExp indUri ->
              AS.ObjectHasValue (renameNamespace tMap opExp)
                                 (renameNamespace tMap indUri)
          AS.ObjectMinCardinality card opExp maybeDesc ->
              AS.ObjectMinCardinality card (renameNamespace tMap opExp)
                                       (maybeRename tMap maybeDesc)
          AS.ObjectMaxCardinality card opExp maybeDesc ->
              AS.ObjectMaxCardinality card (renameNamespace tMap opExp)
                                       (maybeRename tMap maybeDesc)
          AS.ObjectExactCardinality card opExp maybeDesc ->
              AS.ObjectExactCardinality card (renameNamespace tMap opExp)
                                         (maybeRename tMap maybeDesc)
          AS.DataAllValuesFrom dpExp dpExpList dataRange ->
              AS.DataAllValuesFrom (renameNamespace tMap dpExp)
                                    (map (renameNamespace tMap) dpExpList)
                                    (renameNamespace tMap dataRange)
          AS.DataSomeValuesFrom dpExp dpExpList dataRange ->
              AS.DataSomeValuesFrom  (renameNamespace tMap dpExp)
                                      (map (renameNamespace tMap) dpExpList)
                                      (renameNamespace tMap dataRange)
          AS.DataHasValue dpExp const' ->
              AS.DataHasValue (renameNamespace tMap dpExp)
                               (renameNamespace tMap const')
          AS.DataMinCardinality  card dpExp maybeRange ->
              AS.DataMinCardinality card (renameNamespace tMap dpExp)
                                     (maybeRename tMap maybeRange)
          AS.DataMaxCardinality card dpExp maybeRange ->
              AS.DataMaxCardinality  card (renameNamespace tMap dpExp)
                                     (maybeRename tMap maybeRange)
          AS.DataExactCardinality card dpExp maybeRange ->
              AS.DataExactCardinality card (renameNamespace tMap dpExp)
                                       (maybeRename tMap maybeRange)

instance PNamespace AS.SubObjectPropertyExpression where
    propagateNspaces ns subOpExp =
        case subOpExp of
          AS.OPExpression opExp ->
             AS.OPExpression (propagateNspaces ns opExp)
          AS.SubObjectPropertyChain opExpList ->
              AS.SubObjectPropertyChain
                     (map (propagateNspaces ns) opExpList)
    renameNamespace tMap subOpExp =
        case subOpExp of
          AS.OPExpression opExp ->
             AS.OPExpression (renameNamespace tMap opExp)
          AS.SubObjectPropertyChain opExpList ->
              AS.SubObjectPropertyChain
                     (map (renameNamespace tMap) opExpList)

instance PNamespace AS.EntityAnnotation where
    propagateNspaces ns (AS.EntityAnnotation annoList1 entity annoList2) =
        AS.EntityAnnotation (map (propagateNspaces ns) annoList1)
                             (propagateNspaces ns entity)
                             (map (propagateNspaces ns) annoList2)
    renameNamespace tMap (AS.EntityAnnotation annoList1 entity annoList2) =
        AS.EntityAnnotation (map (renameNamespace tMap) annoList1)
                             (renameNamespace tMap entity)
                             (map (renameNamespace tMap) annoList2)


-- propagate namespace of Maybe
maybePropagate :: (PNamespace a) => Namespace -> Maybe a -> Maybe a
maybePropagate ns obj =
    case obj of
             Just j -> Just (propagateNspaces ns j)
             Prelude.Nothing  -> Prelude.Nothing
integrateOntology :: Ontology -> Ontology -> Ontology
integrateOntology onto1@(Ontology oid1 directives1 ns1)
                  onto2@(Ontology oid2 directives2 ns2) =
  if onto1 == onto2 then onto1
   else
    let (newNamespace, transMap) = integrateNamespaces ns1 ns2
    in  Ontology (newOid oid1 oid2)
                 (nub (directives1 ++
                       (map (renameNamespace transMap) directives2)))
                 newNamespace
    where newOid :: Maybe OntologyID -> Maybe OntologyID -> Maybe OntologyID
          newOid Prelude.Nothing Prelude.Nothing = Prelude.Nothing
          newOid Prelude.Nothing oid@(Just _) = oid
          newOid oid@(Just _) Prelude.Nothing = oid
          newOid (Just id1) (Just id2) =
              if id1 == id2 then Just id1
                 else
                 Just (id1 { localPart=
                             (uriToName $ localPart id1) ++
                             "_" ++
                             (uriToName $ uriToName $ localPart id2)})


-- rename namespace of Maybe
maybeRename :: (PNamespace a) => TranslationMap -> Maybe a -> Maybe a
maybeRename tMap obj =
    case obj of
             Just j -> Just (renameNamespace tMap j)
             Prelude.Nothing -> Prelude.Nothing

integrateNamespaces :: Namespace -> Namespace
                    -> (Namespace,TranslationMap)
integrateNamespaces oldNsMap testNsMap =
    if oldNsMap == testNsMap then (oldNsMap, Map.empty)
       else testAndInteg oldNsMap (Map.toList testNsMap) Map.empty

   where testAndInteg :: Namespace -> [(String, String)]
                      -> TranslationMap
                      -> (Namespace, TranslationMap)
         testAndInteg old [] tm = (old, tm)
         testAndInteg old ((pre, uri):r) tm
             | Map.member pre old && uri == (fromJust $ Map.lookup pre old) =
                                           integrateOntology :: Ontology -> Ontology -> Ontology
integrateOntology onto1@(Ontology oid1 directives1 ns1)
                  onto2@(Ontology oid2 directives2 ns2) =
  if onto1 == onto2 then onto1
   else
    let (newNamespace, transMap) = integrateNamespaces ns1 ns2
    in  Ontology (newOid oid1 oid2)
                 (nub (directives1 ++
                       (map (renameNamespace transMap) directives2)))
                 newNamespace
    where newOid :: Maybe OntologyID -> Maybe OntologyID -> Maybe OntologyID
          newOid Prelude.Nothing Prelude.Nothing = Prelude.Nothing
          newOid Prelude.Nothing oid@(Just _) = oid
          newOid oid@(Just _) Prelude.Nothing = oid
          newOid (Just id1) (Just id2) =
              if id1 == id2 then Just id1
                 else
                 Just (id1 { localPart=
                             (uriToName $ localPart id1) ++
                             "_" ++
                             (uriToName $ uriToName $ localPart id2)})

   -- `elem` (Map.elems old) =
                 testAndInteg old r tm
             -- if the uri already existed in old map, the key muss be changed.
             | Map.member uri revMap =
                 testAndInteg old r
                      (Map.insert pre (fromJust $ Map.lookup uri revMap) tm)
             | Map.member pre old =
                let pre' = disambiguateName pre old
                in  testAndInteg (Map.insert pre' uri old) r
                        (Map.insert pre pre' tm)
             | otherwise = testAndInteg (Map.insert pre uri old) r tm
            where revMap = reverseMap old

         disambiguateName :: String -> Namespace -> String
         disambiguateName name nameMap =
             let name' = if isDigit $ head $ reverse name then
                            take ((length name) -1) name
                            else name
             in  fromJust $ find (not . flip Map.member nameMap)
                          [name' ++ (show (i::Int)) | i <-[1..]]


integrateOntologyFile :: AS.OntologyFile -> AS.OntologyFile
                      -> AS.OntologyFile
integrateOntologyFile of1@(AS.OntologyFile ns1
                           (AS.Ontology oid1 imp1 anno1 axiom1))
                      of2@(AS.OntologyFile ns2
                           (AS.Ontology oid2 imp2 anno2 axiom2)) =
  if of1 == of2 then of1
   else
    let (newNamespace, transMap) = integrateNamespaces ns1 ns2
    in  AS.OntologyFile newNamespace
            (AS.Ontology (newOid oid1 oid2)
                 (nub (imp1 ++ (map (renameNamespace transMap) imp2)))
                 (nub (anno1 ++ (map (renameNamespace transMap) anno2)))
                 (nub (axiom1 ++ (map (renameNamespace transMap) axiom2))))

    where newOid :: AS.OntologyURI -> AS.OntologyURI -> AS.OntologyURI
          newOid id1 id2 =
            if null $ localPart id1 then id2 else
             if null $ localPart id2 then id1 else
              if id1 == id2 then id1
                 else id1 {localPart=
                           (uriToName $ localPart id1) ++
                             "_" ++
                             (uriToName $ localPart id2)}

-- | reverse a map: (key, value) -> (value, key)
reverseMap :: (Ord a) => Map.Map k a -> Map.Map a k
reverseMap oldMap =
    Map.foldWithKey transport Map.empty oldMap
  where
   transport :: (Ord a) =>  k -> a -> Map.Map a k -> Map.Map a k
   transport mKey mElem newMap
       | Map.member mElem newMap = error "double keys in translationMap."
       | otherwise = Map.insert mElem mKey newMap

-- build a QName from string, only local part (for node name, etc.).
uriToName :: String -> String
uriToName str =
  if null str then "" else
    let str' = if head str == '"' then
                  read str::String
                  else str
        nodeName = fst $ span (/='/') $ reverse str'
    in  if head nodeName == '#' then
            fst $ span (/='.') (reverse $ tail nodeName)
           else fst $ span (/='.') (reverse nodeName)

-- output a QName for pretty print
printQN :: QName -> String
printQN (QN pre local uri)
            | null pre = show (uri ++ ":" ++ local)
            | otherwise = show (pre ++ ":" ++ local)


