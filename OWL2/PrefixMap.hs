{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(instances for PrefixMap and Named Sentence)

This module implements a namespace transformation
-}

module OWL2.PrefixMap where

import OWL2.Sign
import OWL2.AS
import OWL2.FS
import OWL2.MS
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.AS_Annotation as Common.Annotation
import Data.List (find, nub)
import Data.Maybe
import Data.Char (isDigit, isAlpha)

type TranslationMap = Map.Map String String  -- OldPrefix -> NewPrefix

-- | propagate own namespaces from prefix to namespacesURI within a ontology
class PNamespace a where
    -- | on the basis of translation map changes the prefix of namespace.
    renameNamespace :: TranslationMap -> a -> a

instance PNamespace PrefixMap where
    renameNamespace tMap oldNs =
        foldl (\ ns (pre, ouri) ->
           Map.insert (Map.findWithDefault pre pre tMap) ouri ns)
        Map.empty $ Map.toList oldNs

instance PNamespace QName where
  renameNamespace tMap old = let pre = namePrefix old in
      old { namePrefix = Map.findWithDefault pre pre tMap }

instance PNamespace Sign where
   renameNamespace tMap (Sign p1 p2 p3 p4 p5 p6 p7) =
       Sign (Set.map (renameNamespace tMap) p1)
            (Set.map (renameNamespace tMap) p2)
            (Set.map (renameNamespace tMap) p3)
            (Set.map (renameNamespace tMap) p4)
            (Set.map (renameNamespace tMap) p5)
            (Set.map (renameNamespace tMap) p6)
            (renameNamespace tMap p7)

instance PNamespace (DomainOrRangeOrFunc a) where
   renameNamespace tMap dor = case dor of
     DomainOrRange ty des -> DomainOrRange ty $ renameNamespace tMap des
     RDRange dr -> RDRange $ renameNamespace tMap dr
     _ -> dor

instance PNamespace SignAxiom where
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
    renameNamespace tMap sent = sent {
        Common.Annotation.sentence = renameNamespace tMap
                                     (Common.Annotation.sentence sent) }

instance PNamespace OntologyDocument where
    renameNamespace tMap ( OntologyDocument namespace onto) =
         OntologyDocument (renameNamespace tMap namespace)
                         (renameNamespace tMap onto)

instance PNamespace MOntology where
    renameNamespace tMap ( MOntology ouri impList anList f) =
         MOntology (renameNamespace tMap ouri)
                     (map (renameNamespace tMap) impList)
                     (map (renameNamespace tMap) anList)
                     (map (renameNamespace tMap) f) 

instance PNamespace Annotation where
    renameNamespace tMap anno =
        case anno of
          Annotation annos ap av ->
               Annotation (map (renameNamespace tMap) annos)
                             (renameNamespace tMap ap)
                              (renameNamespace tMap av)

instance PNamespace AnnotationValue where
  renameNamespace ns av = 
        case av of
            AnnValue iri -> AnnValue (renameNamespace ns iri)
            AnnValLit l -> AnnValLit (renameNamespace ns l)
 
instance PNamespace Axiom where
    renameNamespace tMap axiom = case axiom of
        PlainAxiom annosList pa -> PlainAxiom
            (map (renameNamespace tMap) annosList) $ renameNamespace tMap pa

instance PNamespace Annotations where
    renameNamespace tMap ans = map (renameNamespace tMap) ans

instance PNamespace a => PNamespace (AnnotatedList a) where
    renameNamespace tMap anl = AnnotatedList $ map (\ (ans, b) -> (renameNamespace tMap ans, renameNamespace tMap b)) (convertAnnList anl)

instance PNamespace Frame where
    renameNamespace tMap frame = case frame of
        Frame en fb -> Frame (renameNamespace tMap en) (map (renameNamespace tMap) fb)
        MiscFrame ed ans misc -> MiscFrame ed (map (renameNamespace tMap) ans) (renameNamespace tMap misc)
        MiscSameOrDifferent sd ans il -> MiscSameOrDifferent sd (map (renameNamespace tMap) ans) (map (renameNamespace tMap) il)

instance PNamespace FrameBit where
    renameNamespace tMap fb = case fb of
        AnnotationFrameBit ans -> AnnotationFrameBit (map (renameNamespace tMap) ans)
        AnnotationBit r anl -> AnnotationBit r (renameNamespace tMap anl)
        DatatypeBit ans dr -> DatatypeBit (renameNamespace tMap ans) (renameNamespace tMap dr)
        ExpressionBit e anl -> ExpressionBit e (renameNamespace tMap anl)
        ClassDisjointUnion ans cel -> ClassDisjointUnion (renameNamespace tMap ans) (map (renameNamespace tMap) cel)
        ClassHasKey ans ol dl -> ClassHasKey (renameNamespace tMap ans) (map (renameNamespace tMap) ol) (map (renameNamespace tMap) dl)
        ObjectBit r anl -> ObjectBit r (renameNamespace tMap anl)
        ObjectCharacteristics anl -> ObjectCharacteristics anl
        ObjectSubPropertyChain ans ol -> ObjectSubPropertyChain (renameNamespace tMap ans) (map (renameNamespace tMap) ol)
        DataBit r anl -> DataBit r (renameNamespace tMap anl)
        DataPropRange anl -> DataPropRange (renameNamespace tMap anl)
        DataFunctional ans -> DataFunctional (renameNamespace tMap ans)
        IndividualFacts ans -> IndividualFacts (renameNamespace tMap ans)
        IndividualSameOrDifferent sd anl -> IndividualSameOrDifferent sd (renameNamespace tMap anl)

instance PNamespace Fact where
     renameNamespace tMap f = case f of
        ObjectPropertyFact pn op i -> ObjectPropertyFact pn (renameNamespace tMap op) (renameNamespace tMap i)
        DataPropertyFact pn dp l -> DataPropertyFact pn (renameNamespace tMap dp) (renameNamespace tMap l)

instance PNamespace Misc where
    renameNamespace tMap m = case m of
        MiscEquivOrDisjointClasses ce -> MiscEquivOrDisjointClasses $ map (renameNamespace tMap) ce
        MiscEquivOrDisjointObjProp ce -> MiscEquivOrDisjointObjProp $ map (renameNamespace tMap) ce
        MiscEquivOrDisjointDataProp ce -> MiscEquivOrDisjointDataProp $ map (renameNamespace tMap) ce

instance PNamespace PlainAxiom where
    renameNamespace tMap axiom =
        case axiom of
           AnnotationAssertion a -> AnnotationAssertion $ renameNamespace tMap a
           AnnotationAxiom r ap iri -> AnnotationAxiom r (renameNamespace tMap ap) (renameNamespace tMap iri) 
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
           ClassAssertion desc indUri -> ClassAssertion
                   (renameNamespace tMap desc) (renameNamespace tMap indUri) 
           ObjectPropertyAssertion (Assertion objExp ty source target) ->
                   ObjectPropertyAssertion $ Assertion
                   (renameNamespace tMap objExp) ty
                   (renameNamespace tMap source) (renameNamespace tMap target)
           DataPropertyAssertion (Assertion dpExp ty source target) ->
                   DataPropertyAssertion $ Assertion
                   (renameNamespace tMap dpExp) ty
                   (renameNamespace tMap source) (renameNamespace tMap target)
           Declaration entity -> Declaration (renameNamespace tMap entity)
           DatatypeDefinition dt dr -> DatatypeDefinition (renameNamespace tMap dt) (renameNamespace tMap dr)
           HasKey ce opl dpl -> HasKey (renameNamespace tMap ce) (map (renameNamespace tMap) opl) (map (renameNamespace tMap) dpl)

instance PNamespace Entity where
  renameNamespace tMap (Entity ty euri) = Entity ty $ renameNamespace tMap euri

instance PNamespace Literal where
    renameNamespace tMap constant =
        case constant of
           Literal l (Typed curi) ->
               Literal l $ Typed $ renameNamespace tMap curi
           u -> u        -- for untyped constant

instance PNamespace ObjectPropertyExpression where
    renameNamespace tMap opExp =
        case opExp of
           ObjectProp opuri -> ObjectProp (renameNamespace tMap opuri)
           ObjectInverseOf invOp -> ObjectInverseOf (renameNamespace tMap invOp)

instance PNamespace DataRange where
    renameNamespace tMap dr =
        case dr of
           DataType druri restrList ->
               DataType (renameNamespace tMap druri)
                                      (map rnRest restrList)
           DataJunction ty drlist -> DataJunction ty (map (renameNamespace tMap) drlist)
           DataComplementOf dataRange ->
               DataComplementOf (renameNamespace tMap dataRange)
           DataOneOf constList ->
               DataOneOf (map (renameNamespace tMap) constList)
     where rnRest (facet, value) =
               (facet, renameNamespace tMap value)

instance PNamespace ClassExpression where
    renameNamespace tMap desc =
        case desc of
           Expression curi ->
               Expression (renameNamespace tMap curi)
           ObjectJunction ty descList ->
               ObjectJunction ty (map (renameNamespace tMap) descList)
           ObjectComplementOf desc' ->
               ObjectComplementOf (renameNamespace tMap desc')
           ObjectOneOf indsList ->
               ObjectOneOf (map (renameNamespace tMap) indsList)
           ObjectValuesFrom ty opExp desc' ->
               ObjectValuesFrom ty (renameNamespace tMap opExp)
                                      (renameNamespace tMap desc')
           ObjectHasSelf opExp ->
               ObjectHasSelf (renameNamespace tMap opExp)
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
    renameNamespace tMap subOpExp =
        case subOpExp of
           OPExpression opExp ->
              OPExpression (renameNamespace tMap opExp)
           SubObjectPropertyChain opExpList ->
               SubObjectPropertyChain
                     (map (renameNamespace tMap) opExpList)

-- rename namespace of Maybe
maybeRename :: (PNamespace a) => TranslationMap -> Maybe a -> Maybe a
maybeRename tMap = fmap $ renameNamespace tMap

integrateNamespaces :: PrefixMap -> PrefixMap
                    -> (PrefixMap, TranslationMap)
integrateNamespaces oldNsMap testNsMap =
    if oldNsMap == testNsMap then (oldNsMap, Map.empty)
       else testAndInteg oldNsMap (Map.toList testNsMap) Map.empty

   where testAndInteg :: PrefixMap -> [(String, String)]
                      -> TranslationMap
                      -> (PrefixMap, TranslationMap)
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

         disambiguateName :: String -> PrefixMap -> String
         disambiguateName name nameMap =
             let name' = if isDigit $ last name then
                             take (length name - 1) name
                          else name
                      -- how about "reverse . dropWhile isDigit . reverse"?
             in fromJust $ find (not . flip Map.member nameMap)
                     [name' ++ show (i :: Int) | i <- [1 ..]]


integrateOntologyDoc :: OntologyDocument -> OntologyDocument
                      -> OntologyDocument
integrateOntologyDoc of1@( OntologyDocument ns1
                           ( MOntology oid1 imp1 anno1 axiom1))
                      of2@( OntologyDocument ns2
                           ( MOntology oid2 imp2 anno2 axiom2)) =
  if of1 == of2 then of1
   else
    let (newNamespace, transMap) = integrateNamespaces ns1 ns2
        newOid :: OntologyIRI -> OntologyIRI -> OntologyIRI
        newOid id1 id2 = let
              lid1 = localPart id1
              lid2 = localPart id2
            in if null lid1 then id2 else
               if null lid2 || id1 == id2 then id1 else id1
                  { localPart = uriToName lid1 ++ "_" ++ uriToName lid2 }
    in OntologyDocument newNamespace
            ( MOntology (newOid oid1 oid2)
                 (nub $ imp1 ++ map (renameNamespace transMap) imp2)
                 (nub $ anno1 ++ map (renameNamespace transMap) anno2)
                 (nub $ axiom1 ++ map (renameNamespace transMap) (axiom2)))

-- | reverse a map: (key, value) -> (value, key)
reverseMap :: Ord a => Map.Map k a -> Map.Map a k
reverseMap oldMap =
    Map.foldrWithKey transport Map.empty oldMap
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
