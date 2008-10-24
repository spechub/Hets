{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for Namespace and Named Sentence)

This module implements a namespace transformation
-}

module OWL.Namespace
  ( PNamespace(..)
  , integrateNamespaces
  , integrateOntologyFile
  , printQN
  , uriToName) where

import OWL.Sign
import OWL.AS
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.AS_Annotation as Common.Annotation
import Data.List(find, nub)
import Data.Maybe(fromJust)
import Data.Char(isDigit, isAlpha)

type TranslationMap = Map.Map String String  -- OldPrefix -> NewPrefix

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
        foldl (\ ns (pre, ouri) ->
           Map.insert (Map.findWithDefault pre pre tMap) ouri ns)
        Map.empty $ Map.toList oldNs

instance PNamespace QName where
  propagateNspaces ns old@(QN pre local nsUri)
    | null (pre ++ local ++ nsUri) = old
    | otherwise =
     if local == "Thing" || snd (span (/=':') local) == ":Thing" then
        QN "owl" "Thing" "http://www.w3.org/2002/07/owl#"
      else
        if null nsUri then let
          prop :: String -> String -> QName
          prop p loc = QN p loc $ Map.findWithDefault "" p ns
          in if null pre  then
              let (pre', local') = span (/=':')
                                     (if (head local) == '\"' then
                                         read local::String
                                         else local
                                     )
              -- hiding "ftp://" oder "http://" oder "file:///"
              in if length pre' > 3 && isAlpha (head $ reverse pre')
                     || null local' then
                    QN pre' local nsUri
                   else let local'' = tail local'
                         in prop pre' local''
             else prop pre local
         else
             if null pre then
               let (pre', local') = span (/='/')
                                     (if (head nsUri) == '\"' then
                                         read nsUri::String
                                         else nsUri
                                     )
                   rns = reverseMap ns
                in if pre' /= "file:" then
                       old { namePrefix = Map.findWithDefault pre
                             (nsUri ++ "#") rns }
                    -- if uri of QName already existed in namespace map, must
                    -- the prefix also changed (as is located in map).
                   else old { namePrefix = Map.findWithDefault pre
                              (pre' ++ "//" ++ local' ++ "#") rns }
              else old

  renameNamespace tMap old = let pre = namePrefix old in
      old { namePrefix = Map.findWithDefault pre pre tMap }

instance PNamespace Sign where
   propagateNspaces _ sig = sig

   renameNamespace tMap (Sign p1 p2 p3 p4 p5 p6 p7 p8 p9 p10) =
       Sign (renameNamespace tMap p1)
            (Set.map (renameNamespace tMap) p2)
            (Set.map (renameNamespace tMap) p3)
            (Set.map (renameNamespace tMap) p4)
            (Set.map (renameNamespace tMap) p5)
            (Set.map (renameNamespace tMap) p6)
            (Set.map (renameNamespace tMap) p7)
            (Set.map (renameNamespace tMap) p8)
            (Set.map (renameNamespace tMap) p9)
            (renameNamespace tMap p10)

instance PNamespace SignAxiom where
   propagateNspaces _ signAxiom = signAxiom

   renameNamespace tMap signAxiom =
       case signAxiom of
       Subconcept cId1 cId2 ->
           Subconcept (renameNamespace tMap cId1)
                   (renameNamespace tMap cId2)
       RoleDomain id1 rDomains ->
           RoleDomain (renameNamespace tMap id1)
                   (renameNamespace tMap rDomains)
       RoleRange id1 rRange ->
           RoleRange (renameNamespace tMap id1)
                   (renameNamespace tMap rRange)
       FuncRole (t, id1) ->
           FuncRole (t, (renameNamespace tMap id1))
       Conceptmembership iId des ->
           Conceptmembership (renameNamespace tMap iId)
                             (renameNamespace tMap des)
       DataDomain dpExp domain ->
           DataDomain (renameNamespace tMap dpExp)
                      (renameNamespace tMap domain)
       DataRange dpExp range ->
           DataRange (renameNamespace tMap dpExp)
                      (renameNamespace tMap range)
       FuncDataProp dpExp ->
           FuncDataProp (renameNamespace tMap dpExp)
       RefRole (t, opExp) ->
           RefRole (t, (renameNamespace tMap opExp))


instance PNamespace RDomain where
    propagateNspaces _ rd = rd
    renameNamespace tMap rd =
        case rd of
        RDomain des -> RDomain (renameNamespace tMap des)
        DDomain des -> DDomain (renameNamespace tMap des)

instance PNamespace RRange where
   propagateNspaces _ rr = rr

   renameNamespace tMap rr =
        case rr of
         RIRange des -> RIRange (renameNamespace tMap des)
         RDRange dr  -> RDRange (renameNamespace tMap dr)

instance PNamespace Sentence where
   propagateNspaces _ sent = sent

   renameNamespace tMap sent =
       case sent of
       OWLAxiom axiom -> OWLAxiom (renameNamespace tMap axiom)
       OWLFact fact   -> OWLFact  (renameNamespace tMap fact)

instance PNamespace (Common.Annotation.Named Sentence) where
    propagateNspaces _ nsent = nsent

    renameNamespace tMap sent = sent {
        Common.Annotation.sentence = renameNamespace tMap
                                     (Common.Annotation.sentence sent) }

instance PNamespace  OntologyFile where
    propagateNspaces ns ( OntologyFile namespace onto) =
         OntologyFile (propagateNspaces ns namespace)
                    (propagateNspaces ns onto)
    renameNamespace tMap ( OntologyFile namespace onto) =
         OntologyFile (renameNamespace tMap namespace)
                         (renameNamespace tMap onto)

instance PNamespace  Ontology where
    propagateNspaces ns ( Ontology ouri impList anList axList) =
         Ontology (propagateNspaces ns ouri)
                     (map (propagateNspaces ns) impList)
                     (map (propagateNspaces ns) anList)
                     (map (propagateNspaces ns) axList)
    renameNamespace tMap ( Ontology ouri impList anList axList) =
         Ontology (renameNamespace tMap ouri)
                     (map (renameNamespace tMap) impList)
                     (map (renameNamespace tMap) anList)
                     (map (renameNamespace tMap) axList)

instance PNamespace  Annotation where
    propagateNspaces ns anno =
        case anno of
           ExplicitAnnotation annoUri constant ->
               ExplicitAnnotation (propagateNspaces ns annoUri)
                                     (propagateNspaces ns constant)
           Label constant ->
               Label (propagateNspaces ns constant)
           Comment constant ->
               Comment (propagateNspaces ns constant)
           Annotation annoUri entity ->
               Annotation (propagateNspaces ns annoUri)
                             (propagateNspaces ns entity)
    renameNamespace tMap anno =
        case anno of
           ExplicitAnnotation annoUri constant ->
               ExplicitAnnotation (renameNamespace tMap annoUri)
                                     (renameNamespace tMap constant)
           Label constant ->
               Label (renameNamespace tMap constant)
           Comment constant ->
               Comment (renameNamespace tMap constant)
           Annotation annoUri entity ->
               Annotation (renameNamespace tMap annoUri)
                             (renameNamespace tMap entity)


instance PNamespace  Axiom where
    propagateNspaces ns axiom =
        case axiom of
           SubClassOf annosList sub sup ->
               SubClassOf (map (propagateNspaces ns) annosList)
                             (propagateNspaces ns sub)
                             (propagateNspaces ns sup)
           EquivalentClasses annosList descList ->
               EquivalentClasses (map (propagateNspaces ns) annosList)
                                    (map (propagateNspaces ns) descList)
           DisjointClasses annosList descList ->
               DisjointClasses (map (propagateNspaces ns) annosList)
                                  (map (propagateNspaces ns) descList)
           DisjointUnion annosList classUri descList ->
               DisjointUnion (map (propagateNspaces ns) annosList)
                                (propagateNspaces ns classUri)
                                (map (propagateNspaces ns) descList)
           SubObjectPropertyOf annosList subExp objExp ->
               SubObjectPropertyOf (map (propagateNspaces ns) annosList)
                                      (propagateNspaces ns subExp)
                                      (propagateNspaces ns objExp)
           EquivalentObjectProperties annosList objExpList ->
               EquivalentObjectProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) objExpList)
           DisjointObjectProperties annosList objExpList ->
               DisjointObjectProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) objExpList)
           ObjectPropertyDomain annosList objExp desc ->
               ObjectPropertyDomain (map (propagateNspaces ns) annosList)
                                       (propagateNspaces ns objExp)
                                       (propagateNspaces ns desc)
           ObjectPropertyRange annosList objExp desc ->
               ObjectPropertyRange (map (propagateNspaces ns) annosList)
                                      (propagateNspaces ns objExp)
                                      (propagateNspaces ns desc)
           InverseObjectProperties annosList objExp1 objExp2 ->
               InverseObjectProperties (map (propagateNspaces ns) annosList)
                                          (propagateNspaces ns objExp1)
                                          (propagateNspaces ns objExp2)
           FunctionalObjectProperty annosList objExp ->
               FunctionalObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
           InverseFunctionalObjectProperty annosList objExp ->
               InverseFunctionalObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
           ReflexiveObjectProperty annosList objExp ->
               ReflexiveObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
           IrreflexiveObjectProperty annosList objExp ->
               IrreflexiveObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
           SymmetricObjectProperty  annosList objExp ->
               SymmetricObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
           AntisymmetricObjectProperty  annosList objExp ->
               AntisymmetricObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
           TransitiveObjectProperty annosList objExp ->
               TransitiveObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
           SubDataPropertyOf annosList dpExp1 dpExp2 ->
               SubDataPropertyOf (map (propagateNspaces ns) annosList)
                                    (propagateNspaces ns dpExp1)
                                    (propagateNspaces ns dpExp2)
           EquivalentDataProperties annosList dpExpList ->
               EquivalentDataProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) dpExpList)
           DisjointDataProperties annosList  dpExpList ->
               DisjointDataProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) dpExpList)
           DataPropertyDomain annosList dpExp desc ->
               DataPropertyDomain (map (propagateNspaces ns) annosList)
                                     (propagateNspaces ns dpExp)
                                     (propagateNspaces ns desc)
           DataPropertyRange annosList dpExp dataRange ->
               DataPropertyRange (map (propagateNspaces ns) annosList)
                                     (propagateNspaces ns dpExp)
                                     (propagateNspaces ns dataRange)
           FunctionalDataProperty annosList dpExp ->
               FunctionalDataProperty (map (propagateNspaces ns) annosList)
                                         (propagateNspaces ns dpExp)
           SameIndividual annosList indUriList ->
               SameIndividual (map (propagateNspaces ns) annosList)
                                 (map (propagateNspaces ns) indUriList)
           DifferentIndividuals annosList indUriList ->
               DifferentIndividuals  (map (propagateNspaces ns) annosList)
                                        (map (propagateNspaces ns) indUriList)
           ClassAssertion annosList indUri desc ->
               ClassAssertion (map (propagateNspaces ns) annosList)
                                 (propagateNspaces ns indUri)
                                 (propagateNspaces ns desc)
           ObjectPropertyAssertion annosList objExp source target ->
              ObjectPropertyAssertion (map (propagateNspaces ns) annosList)
                                         (propagateNspaces ns objExp)
                                         (propagateNspaces ns source)
                                         (propagateNspaces ns target)
           NegativeObjectPropertyAssertion annosList objExp source target ->
              NegativeObjectPropertyAssertion
                    (map (propagateNspaces ns) annosList)
                    (propagateNspaces ns objExp)
                    (propagateNspaces ns source)
                    (propagateNspaces ns target)
           DataPropertyAssertion annosList dpExp source target ->
               DataPropertyAssertion
                 (map (propagateNspaces ns) annosList)
                 (propagateNspaces ns dpExp)
                 (propagateNspaces ns source)
                 (propagateNspaces ns target)
           NegativeDataPropertyAssertion annosList dpExp source target ->
               NegativeDataPropertyAssertion
                 (map (propagateNspaces ns) annosList)
                 (propagateNspaces ns dpExp)
                 (propagateNspaces ns source)
                 (propagateNspaces ns target)
           Declaration annosList entity ->
               Declaration (map (propagateNspaces ns) annosList)
                              (propagateNspaces ns entity)
           EntityAnno entityAnnotation  ->
               EntityAnno (propagateNspaces ns entityAnnotation)

    renameNamespace tMap axiom =
        case axiom of
           SubClassOf annosList sub sup ->
               SubClassOf (map (renameNamespace tMap) annosList)
                             (renameNamespace tMap sub)
                             (renameNamespace tMap sup)
           EquivalentClasses annosList descList ->
               EquivalentClasses (map (renameNamespace tMap) annosList)
                                    (map (renameNamespace tMap) descList)
           DisjointClasses annosList descList ->
               DisjointClasses (map (renameNamespace tMap) annosList)
                                  (map (renameNamespace tMap) descList)
           DisjointUnion annosList classUri descList ->
               DisjointUnion (map (renameNamespace tMap) annosList)
                                (renameNamespace tMap classUri)
                                (map (renameNamespace tMap) descList)
           SubObjectPropertyOf annosList subExp objExp ->
               SubObjectPropertyOf (map (renameNamespace tMap) annosList)
                                      (renameNamespace tMap subExp)
                                      (renameNamespace tMap objExp)
           EquivalentObjectProperties annosList objExpList ->
               EquivalentObjectProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) objExpList)
           DisjointObjectProperties annosList objExpList ->
               DisjointObjectProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) objExpList)
           ObjectPropertyDomain annosList objExp desc ->
               ObjectPropertyDomain (map (renameNamespace tMap) annosList)
                                       (renameNamespace tMap objExp)
                                       (renameNamespace tMap desc)
           ObjectPropertyRange annosList objExp desc ->
               ObjectPropertyRange (map (renameNamespace tMap) annosList)
                                      (renameNamespace tMap objExp)
                                      (renameNamespace tMap desc)
           InverseObjectProperties annosList objExp1 objExp2 ->
               InverseObjectProperties
                     (map (renameNamespace tMap) annosList)
                     (renameNamespace tMap objExp1)
                     (renameNamespace tMap objExp2)
           FunctionalObjectProperty annosList objExp ->
               FunctionalObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
           InverseFunctionalObjectProperty annosList objExp ->
               InverseFunctionalObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
           ReflexiveObjectProperty annosList objExp ->
               ReflexiveObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
           IrreflexiveObjectProperty annosList objExp ->
               IrreflexiveObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
           SymmetricObjectProperty  annosList objExp ->
               SymmetricObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
           AntisymmetricObjectProperty  annosList objExp ->
               AntisymmetricObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
           TransitiveObjectProperty annosList objExp ->
               TransitiveObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
           SubDataPropertyOf annosList dpExp1 dpExp2 ->
               SubDataPropertyOf (map (renameNamespace tMap) annosList)
                                    (renameNamespace tMap dpExp1)
                                    (renameNamespace tMap dpExp2)
           EquivalentDataProperties annosList dpExpList ->
               EquivalentDataProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) dpExpList)
           DisjointDataProperties annosList  dpExpList ->
               DisjointDataProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) dpExpList)
           DataPropertyDomain annosList dpExp desc ->
               DataPropertyDomain (map (renameNamespace tMap) annosList)
                                     (renameNamespace tMap dpExp)
                                     (renameNamespace tMap desc)
           DataPropertyRange annosList dpExp dataRange ->
               DataPropertyRange (map (renameNamespace tMap) annosList)
                                     (renameNamespace tMap dpExp)
                                     (renameNamespace tMap dataRange)
           FunctionalDataProperty annosList dpExp ->
               FunctionalDataProperty (map (renameNamespace tMap) annosList)
                                         (renameNamespace tMap dpExp)
           SameIndividual annosList indUriList ->
               SameIndividual (map (renameNamespace tMap) annosList)
                                 (map (renameNamespace tMap) indUriList)
           DifferentIndividuals annosList indUriList ->
               DifferentIndividuals  (map (renameNamespace tMap) annosList)
                                        (map (renameNamespace tMap) indUriList)
           ClassAssertion annosList indUri desc ->
               ClassAssertion (map (renameNamespace tMap) annosList)
                                 (renameNamespace tMap indUri)
                                 (renameNamespace tMap desc)
           ObjectPropertyAssertion annosList objExp source target ->
              ObjectPropertyAssertion (map (renameNamespace tMap) annosList)
                                         (renameNamespace tMap objExp)
                                         (renameNamespace tMap source)
                                         (renameNamespace tMap target)
           NegativeObjectPropertyAssertion annosList objExp source target ->
              NegativeObjectPropertyAssertion
                    (map (renameNamespace tMap) annosList)
                    (renameNamespace tMap objExp)
                    (renameNamespace tMap source)
                    (renameNamespace tMap target)
           DataPropertyAssertion annosList dpExp source target ->
               DataPropertyAssertion
                 (map (renameNamespace tMap) annosList)
                 (renameNamespace tMap dpExp)
                 (renameNamespace tMap source)
                 (renameNamespace tMap target)
           NegativeDataPropertyAssertion annosList dpExp source target ->
               NegativeDataPropertyAssertion
                 (map (renameNamespace tMap) annosList)
                 (renameNamespace tMap dpExp)
                 (renameNamespace tMap source)
                 (renameNamespace tMap target)
           Declaration annosList entity ->
               Declaration (map (renameNamespace tMap) annosList)
                              (renameNamespace tMap entity)
           EntityAnno entityAnnotation  ->
               EntityAnno (renameNamespace tMap entityAnnotation)

instance PNamespace  Entity where
    propagateNspaces ns entity =
        case entity of
           Datatype duri ->
               Datatype (propagateNspaces ns duri)
           OWLClassEntity curi ->
               OWLClassEntity (propagateNspaces ns curi)
           ObjectProperty opuri ->
               ObjectProperty (propagateNspaces ns opuri)
           DataProperty dpuri ->
               DataProperty (propagateNspaces ns dpuri)
           Individual iuri ->
               Individual (propagateNspaces ns iuri)
    renameNamespace tMap entity =
        case entity of
           Datatype duri ->
               Datatype (renameNamespace tMap duri)
           OWLClassEntity curi ->
               OWLClassEntity (renameNamespace tMap curi)
           ObjectProperty opuri ->
               ObjectProperty (renameNamespace tMap opuri)
           DataProperty dpuri ->
               DataProperty (renameNamespace tMap dpuri)
           Individual iuri ->
               Individual (renameNamespace tMap iuri)

instance PNamespace  Constant where
    propagateNspaces ns constant =
        case constant of
           TypedConstant (l, curi) ->
               TypedConstant (l, (propagateNspaces ns curi))
           u -> u        -- for untyped constant
    renameNamespace tMap constant =
        case constant of
           TypedConstant (l, curi) ->
               TypedConstant (l, (renameNamespace tMap curi))
           u -> u        -- for untyped constant

instance PNamespace  ObjectPropertyExpression where
    propagateNspaces ns opExp =
        case opExp of
           OpURI opuri ->  OpURI (propagateNspaces ns opuri)
           InverseOp invOp ->  InverseOp (propagateNspaces ns invOp)
    renameNamespace tMap opExp =
        case opExp of
           OpURI opuri ->  OpURI (renameNamespace tMap opuri)
           InverseOp invOp ->  InverseOp (renameNamespace tMap invOp)

instance PNamespace  DataRange where
    propagateNspaces ns dr =
        case dr of
           DRDatatype druri ->
               DRDatatype (propagateNspaces ns druri)
           DataComplementOf dataRange ->
               DataComplementOf (propagateNspaces ns dataRange)
           DataOneOf constList ->
               DataOneOf (map (propagateNspaces ns) constList)
           DatatypeRestriction dataRange restrList ->
               DatatypeRestriction (propagateNspaces ns dataRange)
                                      (map pnRest restrList)
     where pnRest (facet, value) =
               (facet, propagateNspaces ns value)
    renameNamespace tMap dr =
        case dr of
           DRDatatype druri ->
               DRDatatype (renameNamespace tMap druri)
           DataComplementOf dataRange ->
               DataComplementOf (renameNamespace tMap dataRange)
           DataOneOf constList ->
               DataOneOf (map (renameNamespace tMap) constList)
           DatatypeRestriction dataRange restrList ->
               DatatypeRestriction (renameNamespace tMap dataRange)
                                      (map rnRest restrList)
     where rnRest (facet, value) =
               (facet, renameNamespace tMap value)

instance PNamespace  Description where
    propagateNspaces ns desc =
        case desc of
           OWLClass curi ->
               OWLClass (propagateNspaces ns curi)
           ObjectUnionOf descList ->
               ObjectUnionOf (map (propagateNspaces ns) descList)
           ObjectIntersectionOf descList ->
               ObjectIntersectionOf (map (propagateNspaces ns) descList)
           ObjectComplementOf desc' ->
               ObjectComplementOf  (propagateNspaces ns desc')
           ObjectOneOf indsList ->
               ObjectOneOf (map (propagateNspaces ns) indsList)
           ObjectAllValuesFrom opExp desc' ->
               ObjectAllValuesFrom (propagateNspaces ns opExp)
                                      (propagateNspaces ns desc')
           ObjectSomeValuesFrom opExp desc' ->
               ObjectSomeValuesFrom (propagateNspaces ns opExp)
                                       (propagateNspaces ns desc')
           ObjectExistsSelf opExp ->
               ObjectExistsSelf (propagateNspaces ns opExp)
           ObjectHasValue opExp indUri ->
               ObjectHasValue (propagateNspaces ns opExp)
                                 (propagateNspaces ns indUri)
           ObjectMinCardinality card opExp maybeDesc ->
               ObjectMinCardinality card (propagateNspaces ns opExp)
                                       (maybePropagate ns maybeDesc)
           ObjectMaxCardinality card opExp maybeDesc ->
               ObjectMaxCardinality card (propagateNspaces ns opExp)
                                       (maybePropagate ns maybeDesc)
           ObjectExactCardinality card opExp maybeDesc ->
               ObjectExactCardinality card (propagateNspaces ns opExp)
                                         (maybePropagate ns maybeDesc)
           DataAllValuesFrom dpExp dpExpList dataRange ->
               DataAllValuesFrom (propagateNspaces ns dpExp)
                                    (map (propagateNspaces ns) dpExpList)
                                    (propagateNspaces ns dataRange)
           DataSomeValuesFrom dpExp dpExpList dataRange ->
               DataSomeValuesFrom  (propagateNspaces ns dpExp)
                                      (map (propagateNspaces ns) dpExpList)
                                      (propagateNspaces ns dataRange)
           DataHasValue dpExp const' ->
               DataHasValue (propagateNspaces ns dpExp)
                               (propagateNspaces ns const')
           DataMinCardinality  card dpExp maybeRange ->
               DataMinCardinality card (propagateNspaces ns dpExp)
                                     (maybePropagate ns maybeRange)
           DataMaxCardinality card dpExp maybeRange ->
               DataMaxCardinality  card (propagateNspaces ns dpExp)
                                     (maybePropagate ns maybeRange)
           DataExactCardinality card dpExp maybeRange ->
               DataExactCardinality card (propagateNspaces ns dpExp)
                                       (maybePropagate ns maybeRange)

    renameNamespace tMap desc =
        case desc of
           OWLClass curi ->
               OWLClass (renameNamespace tMap curi)
           ObjectUnionOf descList ->
               ObjectUnionOf (map (renameNamespace tMap) descList)
           ObjectIntersectionOf descList ->
               ObjectIntersectionOf (map (renameNamespace tMap) descList)
           ObjectComplementOf desc' ->
               ObjectComplementOf  (renameNamespace tMap desc')
           ObjectOneOf indsList ->
               ObjectOneOf (map (renameNamespace tMap) indsList)
           ObjectAllValuesFrom opExp desc' ->
               ObjectAllValuesFrom (renameNamespace tMap opExp)
                                      (renameNamespace tMap desc')
           ObjectSomeValuesFrom opExp desc' ->
               ObjectSomeValuesFrom (renameNamespace tMap opExp)
                                       (renameNamespace tMap desc')
           ObjectExistsSelf opExp ->
               ObjectExistsSelf (renameNamespace tMap opExp)
           ObjectHasValue opExp indUri ->
               ObjectHasValue (renameNamespace tMap opExp)
                                 (renameNamespace tMap indUri)
           ObjectMinCardinality card opExp maybeDesc ->
               ObjectMinCardinality card (renameNamespace tMap opExp)
                                       (maybeRename tMap maybeDesc)
           ObjectMaxCardinality card opExp maybeDesc ->
               ObjectMaxCardinality card (renameNamespace tMap opExp)
                                       (maybeRename tMap maybeDesc)
           ObjectExactCardinality card opExp maybeDesc ->
               ObjectExactCardinality card (renameNamespace tMap opExp)
                                         (maybeRename tMap maybeDesc)
           DataAllValuesFrom dpExp dpExpList dataRange ->
               DataAllValuesFrom (renameNamespace tMap dpExp)
                                    (map (renameNamespace tMap) dpExpList)
                                    (renameNamespace tMap dataRange)
           DataSomeValuesFrom dpExp dpExpList dataRange ->
               DataSomeValuesFrom  (renameNamespace tMap dpExp)
                                      (map (renameNamespace tMap) dpExpList)
                                      (renameNamespace tMap dataRange)
           DataHasValue dpExp const' ->
               DataHasValue (renameNamespace tMap dpExp)
                               (renameNamespace tMap const')
           DataMinCardinality  card dpExp maybeRange ->
               DataMinCardinality card (renameNamespace tMap dpExp)
                                     (maybeRename tMap maybeRange)
           DataMaxCardinality card dpExp maybeRange ->
               DataMaxCardinality  card (renameNamespace tMap dpExp)
                                     (maybeRename tMap maybeRange)
           DataExactCardinality card dpExp maybeRange ->
               DataExactCardinality card (renameNamespace tMap dpExp)
                                       (maybeRename tMap maybeRange)

instance PNamespace  SubObjectPropertyExpression where
    propagateNspaces ns subOpExp =
        case subOpExp of
           OPExpression opExp ->
              OPExpression (propagateNspaces ns opExp)
           SubObjectPropertyChain opExpList ->
               SubObjectPropertyChain
                     (map (propagateNspaces ns) opExpList)
    renameNamespace tMap subOpExp =
        case subOpExp of
           OPExpression opExp ->
              OPExpression (renameNamespace tMap opExp)
           SubObjectPropertyChain opExpList ->
               SubObjectPropertyChain
                     (map (renameNamespace tMap) opExpList)

instance PNamespace  EntityAnnotation where
    propagateNspaces ns ( EntityAnnotation annoList1 entity annoList2) =
         EntityAnnotation (map (propagateNspaces ns) annoList1)
                             (propagateNspaces ns entity)
                             (map (propagateNspaces ns) annoList2)
    renameNamespace tMap ( EntityAnnotation annoList1 entity annoList2) =
         EntityAnnotation (map (renameNamespace tMap) annoList1)
                             (renameNamespace tMap entity)
                             (map (renameNamespace tMap) annoList2)


-- propagate namespace of Maybe
maybePropagate :: (PNamespace a) => Namespace -> Maybe a -> Maybe a
maybePropagate ns = fmap $ propagateNspaces ns

-- rename namespace of Maybe
maybeRename :: (PNamespace a) => TranslationMap -> Maybe a -> Maybe a
maybeRename tMap = fmap $ renameNamespace tMap

integrateNamespaces :: Namespace -> Namespace
                    -> (Namespace,TranslationMap)
integrateNamespaces oldNsMap testNsMap =
    if oldNsMap == testNsMap then (oldNsMap, Map.empty)
       else testAndInteg oldNsMap (Map.toList testNsMap) Map.empty

   where testAndInteg :: Namespace -> [(String, String)]
                      -> TranslationMap
                      -> (Namespace, TranslationMap)
         testAndInteg old [] tm = (old, tm)
         testAndInteg old ((pre, ouri):r) tm
             | Map.member pre old && ouri ==
               (fromJust $ Map.lookup pre old) =
   -- `elem` (Map.elems old) =
                 testAndInteg old r tm
             -- if the uri already existed in old map, the key muss be changed.
             | Map.member ouri revMap =
                 testAndInteg old r
                      (Map.insert pre (fromJust $ Map.lookup ouri revMap) tm)
             | Map.member pre old =
                let pre' = disambiguateName pre old
                in  testAndInteg (Map.insert pre' ouri old) r
                        (Map.insert pre pre' tm)
             | otherwise = testAndInteg (Map.insert pre ouri old) r tm
            where revMap = reverseMap old

         disambiguateName :: String -> Namespace -> String
         disambiguateName name nameMap =
             let name' = if isDigit $ head $ reverse name then
                             take ((length name) -1) name
                          else name
             in  fromJust $ find (not . flip Map.member nameMap)
                     [name' ++ (show (i::Int)) | i <-[1..]]


integrateOntologyFile ::  OntologyFile ->  OntologyFile
                      ->  OntologyFile
integrateOntologyFile of1@( OntologyFile ns1
                           ( Ontology oid1 imp1 anno1 axiom1))
                      of2@( OntologyFile ns2
                           ( Ontology oid2 imp2 anno2 axiom2)) =
  if of1 == of2 then of1
   else
    let (newNamespace, transMap) = integrateNamespaces ns1 ns2
    in   OntologyFile newNamespace
            ( Ontology (newOid oid1 oid2)
                 (nub (imp1 ++ (map (renameNamespace transMap) imp2)))
                 (nub (anno1 ++ (map (renameNamespace transMap) anno2)))
                 (nub (axiom1 ++ (map (renameNamespace transMap) axiom2))))

    where newOid ::  OntologyURI ->  OntologyURI ->  OntologyURI
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
uriToName str = let str' = if take 1 str == "\"" then read str else str in
    takeWhile (/='.') $ reverse $ case takeWhile (/='/') $ reverse str' of
         '#' : r  -> r
         r -> r

-- output a QName for pretty print
printQN :: QName -> String
printQN (QN pre local u)
            | null pre = show (u ++ ":" ++ local)
            | otherwise = show (pre ++ ":" ++ local)
