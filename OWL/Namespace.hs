{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(instances for Namespace and Named Sentence)

This module implements a namespace transformation
-}

module OWL.Namespace
  ( PNamespace (..)
  , integrateNamespaces
  , integrateOntologyFile
  , uriToName) where

import OWL.Sign
import OWL.AS
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.AS_Annotation as Common.Annotation
import Data.List (find, nub)
import Data.Maybe
import Data.Char (isDigit, isAlpha)

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
  propagateNspaces ns old@(QN pre local isFull nsUri)
    | null (pre ++ local ++ nsUri) = old
    | otherwise =
     if local == "Thing" || snd (span (/= ':') local) == ":Thing" then
        QN "owl" "Thing" False "http://www.w3.org/2002/07/owl#"
      else
        if null nsUri then let
          prop :: String -> String -> QName
          prop p loc = QN p loc isFull $ Map.findWithDefault "" p ns
          in if null pre then
              let (pre', local') = span (/= ':')
                                     (if head local == '\"' then
                                         read local :: String
                                         else local
                                     )
              -- hiding "ftp://" oder "http://" oder "file:///"
              in if null local' then old else let local'' = tail local' in
                    if length pre' > 3 && isAlpha (last pre') then old
                   else prop pre' local''
             else prop pre local
         else
             if null pre then
               let (pre', local') = span (/= '/')
                                     (if head nsUri == '\"' then
                                         read nsUri :: String
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
   renameNamespace tMap (Sign p1 p2 p3 p4 p5 p6 p7 p8 p10) =
       Sign (renameNamespace tMap p1)
            (Set.map (renameNamespace tMap) p2)
            (Set.map (renameNamespace tMap) p3)
            (Set.map (renameNamespace tMap) p4)
            (Set.map (renameNamespace tMap) p5)
            (Set.map (renameNamespace tMap) p6)
            (Set.map (renameNamespace tMap) p7)
            (Set.map (renameNamespace tMap) p8)
            (renameNamespace tMap p10)

instance PNamespace (DomainOrRangeOrFunc a) where
   propagateNspaces _ = id
   renameNamespace tMap dor = case dor of
     DomainOrRange ty des -> DomainOrRange ty $ renameNamespace tMap des
     RDRange dr -> RDRange $ renameNamespace tMap dr
     _ -> dor

instance PNamespace SignAxiom where
   propagateNspaces _ = id
   renameNamespace tMap signAxiom =
       case signAxiom of
       Subconcept cId1 cId2 ->
           Subconcept (renameNamespace tMap cId1)
                   (renameNamespace tMap cId2)
       Role rdr id1 ->
           Role (renameNamespace tMap rdr) (renameNamespace tMap id1)
       Data rdr id1 ->
           Data (renameNamespace tMap rdr) (renameNamespace tMap id1)
       Conceptmembership iId des ->
           Conceptmembership (renameNamespace tMap iId)
                             (renameNamespace tMap des)

instance PNamespace (Common.Annotation.Named Axiom) where
    propagateNspaces _ nsent = nsent
    renameNamespace tMap sent = sent {
        Common.Annotation.sentence = renameNamespace tMap
                                     (Common.Annotation.sentence sent) }

instance PNamespace OntologyFile where
    propagateNspaces ns ( OntologyFile namespace onto) =
         OntologyFile (propagateNspaces ns namespace)
                    (propagateNspaces ns onto)
    renameNamespace tMap ( OntologyFile namespace onto) =
         OntologyFile (renameNamespace tMap namespace)
                         (renameNamespace tMap onto)

instance PNamespace Ontology where
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

instance PNamespace Annotation where
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

instance PNamespace Axiom where
    propagateNspaces ns axiom = case axiom of
        PlainAxiom annosList pa -> PlainAxiom
            (map (propagateNspaces ns) annosList) $ propagateNspaces ns pa
        EntityAnno entityAnnotation ->
            EntityAnno (propagateNspaces ns entityAnnotation)
    renameNamespace tMap axiom = case axiom of
        PlainAxiom annosList pa -> PlainAxiom
            (map (renameNamespace tMap) annosList) $ renameNamespace tMap pa
        EntityAnno entityAnnotation ->
               EntityAnno (renameNamespace tMap entityAnnotation)

instance PNamespace PlainAxiom where
    propagateNspaces ns axiom =
        case axiom of
           SubClassOf sub sup -> SubClassOf
                   (propagateNspaces ns sub) (propagateNspaces ns sup)
           EquivOrDisjointClasses ty descList -> EquivOrDisjointClasses ty
                   (map (propagateNspaces ns) descList)
           DisjointUnion classUri descList -> DisjointUnion
                   (propagateNspaces ns classUri)
                   (map (propagateNspaces ns) descList)
           SubObjectPropertyOf subExp objExp -> SubObjectPropertyOf
                   (propagateNspaces ns subExp) (propagateNspaces ns objExp)
           EquivOrDisjointObjectProperties ty objExpList ->
                   EquivOrDisjointObjectProperties ty
                   (map (propagateNspaces ns) objExpList)
           ObjectPropertyDomainOrRange ty objExp desc ->
                   ObjectPropertyDomainOrRange ty
                   (propagateNspaces ns objExp) (propagateNspaces ns desc)
           InverseObjectProperties objExp1 objExp2 -> InverseObjectProperties
                   (propagateNspaces ns objExp1) (propagateNspaces ns objExp2)
           ObjectPropertyCharacter ch objExp -> ObjectPropertyCharacter ch
                   (propagateNspaces ns objExp)
           SubDataPropertyOf dpExp1 dpExp2 -> SubDataPropertyOf
                   (propagateNspaces ns dpExp1) (propagateNspaces ns dpExp2)
           EquivOrDisjointDataProperties ty dpExpList ->
                   EquivOrDisjointDataProperties ty
                   (map (propagateNspaces ns) dpExpList)
           DataPropertyDomainOrRange ddr dpExp -> DataPropertyDomainOrRange
                   (case ddr of
                      DataDomain desc -> DataDomain $ propagateNspaces ns desc
                      DataRange dataRange -> DataRange
                          $ propagateNspaces ns dataRange)
                   $ propagateNspaces ns dpExp
           FunctionalDataProperty dpExp -> FunctionalDataProperty
                   (propagateNspaces ns dpExp)
           SameOrDifferentIndividual ty indUriList ->
                   SameOrDifferentIndividual ty
                   (map (propagateNspaces ns) indUriList)
           ClassAssertion indUri desc -> ClassAssertion
                   (propagateNspaces ns indUri) (propagateNspaces ns desc)
           ObjectPropertyAssertion (Assertion objExp ty source target) ->
                   ObjectPropertyAssertion $ Assertion
                   (propagateNspaces ns objExp) ty
                   (propagateNspaces ns source) (propagateNspaces ns target)
           DataPropertyAssertion (Assertion dpExp ty source target) ->
                   DataPropertyAssertion $ Assertion
                   (propagateNspaces ns dpExp) ty
                   (propagateNspaces ns source) (propagateNspaces ns target)
           Declaration entity -> Declaration (propagateNspaces ns entity)
    renameNamespace tMap axiom =
        case axiom of
           SubClassOf sub sup -> SubClassOf
                   (renameNamespace tMap sub) (renameNamespace tMap sup)
           EquivOrDisjointClasses ty descList -> EquivOrDisjointClasses ty
                   (map (renameNamespace tMap) descList)
           DisjointUnion classUri descList -> DisjointUnion
                   (renameNamespace tMap classUri)
                   (map (renameNamespace tMap) descList)
           SubObjectPropertyOf subExp objExp -> SubObjectPropertyOf
                   (renameNamespace tMap subExp)
                   (renameNamespace tMap objExp)
           EquivOrDisjointObjectProperties ty objExpList ->
                   EquivOrDisjointObjectProperties ty
                   (map (renameNamespace tMap) objExpList)
           ObjectPropertyDomainOrRange ty objExp desc ->
                   ObjectPropertyDomainOrRange ty
                   (renameNamespace tMap objExp) (renameNamespace tMap desc)
           InverseObjectProperties objExp1 objExp2 -> InverseObjectProperties
                   (renameNamespace tMap objExp1)
                   (renameNamespace tMap objExp2)
           ObjectPropertyCharacter ch objExp -> ObjectPropertyCharacter ch
                   (renameNamespace tMap objExp)
           SubDataPropertyOf dpExp1 dpExp2 -> SubDataPropertyOf
                   (renameNamespace tMap dpExp1) (renameNamespace tMap dpExp2)
           EquivOrDisjointDataProperties ty dpExpList ->
                   EquivOrDisjointDataProperties ty
                   (map (renameNamespace tMap) dpExpList)
           DataPropertyDomainOrRange ddr dpExp -> DataPropertyDomainOrRange
                   (case ddr of
                      DataDomain desc -> DataDomain $ renameNamespace tMap desc
                      DataRange dataRange -> DataRange
                          $ renameNamespace tMap dataRange)
                   (renameNamespace tMap dpExp)
           FunctionalDataProperty dpExp -> FunctionalDataProperty
                   (renameNamespace tMap dpExp)
           SameOrDifferentIndividual ty indUriList ->
                   SameOrDifferentIndividual ty
                   (map (renameNamespace tMap) indUriList)
           ClassAssertion indUri desc -> ClassAssertion
                   (renameNamespace tMap indUri) (renameNamespace tMap desc)
           ObjectPropertyAssertion (Assertion objExp ty source target) ->
                   ObjectPropertyAssertion $ Assertion
                   (renameNamespace tMap objExp) ty
                   (renameNamespace tMap source) (renameNamespace tMap target)
           DataPropertyAssertion (Assertion dpExp ty source target) ->
                   DataPropertyAssertion $ Assertion
                   (renameNamespace tMap dpExp) ty
                   (renameNamespace tMap source) (renameNamespace tMap target)
           Declaration entity -> Declaration (renameNamespace tMap entity)

instance PNamespace Entity where
  propagateNspaces ns (Entity ty euri) = Entity ty $ propagateNspaces ns euri
  renameNamespace tMap (Entity ty euri) = Entity ty $ renameNamespace tMap euri

instance PNamespace Constant where
    propagateNspaces ns constant =
        case constant of
           Constant l (Typed curi) ->
               Constant l $ Typed $ propagateNspaces ns curi
           u -> u        -- for untyped constant
    renameNamespace tMap constant =
        case constant of
           Constant l (Typed curi) ->
               Constant l $ Typed $ renameNamespace tMap curi
           u -> u        -- for untyped constant

instance PNamespace ObjectPropertyExpression where
    propagateNspaces ns opExp =
        case opExp of
           OpURI opuri -> OpURI (propagateNspaces ns opuri)
           InverseOp invOp -> InverseOp (propagateNspaces ns invOp)
    renameNamespace tMap opExp =
        case opExp of
           OpURI opuri -> OpURI (renameNamespace tMap opuri)
           InverseOp invOp -> InverseOp (renameNamespace tMap invOp)

instance PNamespace DataRange where
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

instance PNamespace Description where
    propagateNspaces ns desc =
        case desc of
           OWLClassDescription curi ->
               OWLClassDescription (propagateNspaces ns curi)
           ObjectJunction ty descList ->
               ObjectJunction ty (map (propagateNspaces ns) descList)
           ObjectComplementOf desc' ->
               ObjectComplementOf (propagateNspaces ns desc')
           ObjectOneOf indsList ->
               ObjectOneOf (map (propagateNspaces ns) indsList)
           ObjectValuesFrom ty opExp desc' ->
               ObjectValuesFrom ty (propagateNspaces ns opExp)
                                      (propagateNspaces ns desc')
           ObjectExistsSelf opExp ->
               ObjectExistsSelf (propagateNspaces ns opExp)
           ObjectHasValue opExp indUri ->
               ObjectHasValue (propagateNspaces ns opExp)
                                 (propagateNspaces ns indUri)
           ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
               ObjectCardinality $ Cardinality ty card
                 (propagateNspaces ns opExp) (maybePropagate ns maybeDesc)
           DataValuesFrom ty dpExp dpExpList dataRange ->
               DataValuesFrom ty (propagateNspaces ns dpExp)
                                    (map (propagateNspaces ns) dpExpList)
                                    (propagateNspaces ns dataRange)
           DataHasValue dpExp const' ->
               DataHasValue (propagateNspaces ns dpExp)
                               (propagateNspaces ns const')
           DataCardinality (Cardinality ty card dpExp maybeRange) ->
               DataCardinality $ Cardinality ty card
                 (propagateNspaces ns dpExp) (maybePropagate ns maybeRange)
    renameNamespace tMap desc =
        case desc of
           OWLClassDescription curi ->
               OWLClassDescription (renameNamespace tMap curi)
           ObjectJunction ty descList ->
               ObjectJunction ty (map (renameNamespace tMap) descList)
           ObjectComplementOf desc' ->
               ObjectComplementOf (renameNamespace tMap desc')
           ObjectOneOf indsList ->
               ObjectOneOf (map (renameNamespace tMap) indsList)
           ObjectValuesFrom ty opExp desc' ->
               ObjectValuesFrom ty (renameNamespace tMap opExp)
                                      (renameNamespace tMap desc')
           ObjectExistsSelf opExp ->
               ObjectExistsSelf (renameNamespace tMap opExp)
           ObjectHasValue opExp indUri ->
               ObjectHasValue (renameNamespace tMap opExp)
                                 (renameNamespace tMap indUri)
           ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
               ObjectCardinality $ Cardinality ty card
                 (renameNamespace tMap opExp) (maybeRename tMap maybeDesc)
           DataValuesFrom ty dpExp dpExpList dataRange ->
               DataValuesFrom ty (renameNamespace tMap dpExp)
                                    (map (renameNamespace tMap) dpExpList)
                                    (renameNamespace tMap dataRange)
           DataHasValue dpExp const' ->
               DataHasValue (renameNamespace tMap dpExp)
                               (renameNamespace tMap const')
           DataCardinality (Cardinality ty card dpExp maybeRange) ->
               DataCardinality $ Cardinality ty card
                 (renameNamespace tMap dpExp) (maybeRename tMap maybeRange)

instance PNamespace SubObjectPropertyExpression where
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

instance PNamespace EntityAnnotation where
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
                    -> (Namespace, TranslationMap)
integrateNamespaces oldNsMap testNsMap =
    if oldNsMap == testNsMap then (oldNsMap, Map.empty)
       else testAndInteg oldNsMap (Map.toList testNsMap) Map.empty

   where testAndInteg :: Namespace -> [(String, String)]
                      -> TranslationMap
                      -> (Namespace, TranslationMap)
         testAndInteg old [] tm = (old, tm)
         testAndInteg old ((pre, ouri) : r) tm
             | Just ouri == Map.lookup pre old =
                 testAndInteg old r tm
             -- if the uri already existed in old map, the key must be changed.
             | isJust val =
                 testAndInteg old r
                      (Map.insert pre (fromJust val) tm)
             | Map.member pre old =
                let pre' = disambiguateName pre old
                in testAndInteg (Map.insert pre' ouri old) r
                        (Map.insert pre pre' tm)
             | otherwise = testAndInteg (Map.insert pre ouri old) r tm
            where val = Map.lookup ouri $ reverseMap old

         disambiguateName :: String -> Namespace -> String
         disambiguateName name nameMap =
             let name' = if isDigit $ last name then
                             take (length name - 1) name
                          else name
                      -- how about "reverse . dropWhile isDigit . reverse"?
             in fromJust $ find (not . flip Map.member nameMap)
                     [name' ++ show (i :: Int) | i <- [1 ..]]


integrateOntologyFile :: OntologyFile -> OntologyFile
                      -> OntologyFile
integrateOntologyFile of1@( OntologyFile ns1
                           ( Ontology oid1 imp1 anno1 axiom1))
                      of2@( OntologyFile ns2
                           ( Ontology oid2 imp2 anno2 axiom2)) =
  if of1 == of2 then of1
   else
    let (newNamespace, transMap) = integrateNamespaces ns1 ns2
        newOid :: OntologyURI -> OntologyURI -> OntologyURI
        newOid id1 id2 = let
              lid1 = localPart id1
              lid2 = localPart id2
            in if null lid1 then id2 else
               if null lid2 || id1 == id2 then id1 else id1
                  { localPart = uriToName lid1 ++ "_" ++ uriToName lid2 }
    in OntologyFile newNamespace
            ( Ontology (newOid oid1 oid2)
                 (nub $ imp1 ++ map (renameNamespace transMap) imp2)
                 (nub $ anno1 ++ map (renameNamespace transMap) anno2)
                 (nub $ axiom1 ++ map (renameNamespace transMap) axiom2))

-- | reverse a map: (key, value) -> (value, key)
reverseMap :: Ord a => Map.Map k a -> Map.Map a k
reverseMap oldMap =
    Map.foldWithKey transport Map.empty oldMap
  where
   transport :: Ord a => k -> a -> Map.Map a k -> Map.Map a k
   transport mKey mElem newMap
       | Map.member mElem newMap = error "double keys in translationMap."
       | otherwise = Map.insert mElem mKey newMap

-- build a QName from string, only local part (for node name, etc.).
uriToName :: String -> String
uriToName str = let
  str' = case str of
           '"' : _ -> read str
           _ -> str
  in takeWhile (/= '.') $ reverse $ case takeWhile (/= '/') $ reverse str' of
         '#' : r -> r
         r -> r
