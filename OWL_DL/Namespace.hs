{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for Namespace and Named Sentence)

This module implements a namespace transformation
-}

module OWL_DL.Namespace where

import OWL_DL.AS
import OWL_DL.Sign
import qualified OWL_DL.OWL11.Sign as OS11
import qualified OWL_DL.OWL11.FFS as FFS
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

instance PNamespace Ontology where
    propagateNspaces ns onto =
        case onto of
        Ontology maybeID directives ons ->
            Ontology (maybePropagate ns maybeID)
                     (map (propagateNspaces ns) directives)
                     ons
    renameNamespace tMap onto =
        case onto of
        Ontology maybeID directives ns ->
            Ontology (maybeRename ns maybeID)
                     (map (renameNamespace tMap) directives)
                     (renameNamespace tMap ns)

instance PNamespace Directive where
    propagateNspaces ns directiv =
        case directiv of
        Anno annotation -> Anno (propagateNspaces ns annotation)
        Ax axiom        -> Ax (propagateNspaces ns axiom)
        Fc fact         -> Fc (propagateNspaces ns fact)
    renameNamespace tMap directiv =
        case directiv of
        Anno annotation -> Anno (renameNamespace tMap annotation)
        Ax axiom        -> Ax (renameNamespace tMap axiom)
        Fc fact         -> Fc (renameNamespace tMap fact)

instance PNamespace Annotation where
    propagateNspaces ns annotation =
        case annotation of
        OntoAnnotation opID oID ->
            OntoAnnotation (propagateNspaces ns opID) (propagateNspaces ns oID)
        URIAnnotation apID uri  ->
            URIAnnotation (propagateNspaces ns apID) (propagateNspaces ns uri)
        DLAnnotation apID dl    ->
            DLAnnotation (propagateNspaces ns apID) dl
        IndivAnnotation apID ind->
            IndivAnnotation (propagateNspaces ns apID)
                            (propagateNspaces ns ind)
    renameNamespace tMap annotation =
        case annotation of
        OntoAnnotation opID oID ->
            OntoAnnotation (renameNamespace tMap opID)
                               (renameNamespace tMap oID)
        URIAnnotation apID uri  ->
            URIAnnotation (renameNamespace tMap  apID)
                              (renameNamespace tMap  uri)
        DLAnnotation apID dl    ->
            DLAnnotation (renameNamespace tMap  apID) dl
        IndivAnnotation apID ind->
            IndivAnnotation (renameNamespace tMap  apID)
                            (renameNamespace tMap  ind)

instance PNamespace Fact where
    propagateNspaces ns fact =
        case fact of
        Indiv ind                     ->
            Indiv (propagateNspaces ns ind)
        SameIndividual iID1 iID2 iIDs ->
            SameIndividual (propagateNspaces ns iID1)
                               (propagateNspaces ns iID2)
                               (map (propagateNspaces ns) iIDs)
        DifferentIndividuals iID1 iID2 iIDs ->
            DifferentIndividuals (propagateNspaces ns iID1)
                                     (propagateNspaces ns iID2)
                                     (map (propagateNspaces ns) iIDs)
    renameNamespace tMap fact =
        case fact of
        Indiv ind                     ->
            Indiv (renameNamespace tMap ind)
        SameIndividual iID1 iID2 iIDs ->
            SameIndividual (renameNamespace tMap iID1)
                               (renameNamespace tMap iID2)
                               (map (renameNamespace tMap) iIDs)
        DifferentIndividuals iID1 iID2 iIDs ->
            DifferentIndividuals (renameNamespace tMap iID1)
                                     (renameNamespace tMap iID2)
                                     (map (renameNamespace tMap) iIDs)

instance PNamespace Individual where
    propagateNspaces ns indiv =
        case indiv of
        Individual maybeIID annos types values ->
            Individual (maybePropagate ns maybeIID)
                           (map (propagateNspaces ns) annos)
                           (map (propagateNspaces ns) types)
                           (map (propagateNspaces ns) values)

    renameNamespace tMap indiv =
        case indiv of
        Individual maybeIID annos types values ->
            Individual (maybeRename tMap maybeIID)
                           (map (renameNamespace tMap) annos)
                           (map (renameNamespace tMap) types)
                           (map (renameNamespace tMap) values)

instance PNamespace Value where
    propagateNspaces ns value =
        case value of
        ValueID ivpID iID        ->
            ValueID (propagateNspaces ns ivpID)
                   (propagateNspaces ns iID)
        ValueIndiv ivpID individual ->
            ValueIndiv (propagateNspaces ns ivpID)
                       (propagateNspaces ns individual)
        ValueDL dvpID dl -> ValueDL (propagateNspaces ns dvpID) dl

    renameNamespace tMap value =
        case value of
        ValueID ivpID iID        ->
            ValueID (renameNamespace tMap ivpID)
                   (renameNamespace tMap iID)
        ValueIndiv ivpID individual ->
            ValueIndiv (renameNamespace tMap ivpID)
                       (renameNamespace tMap individual)
        ValueDL dvpID dl -> ValueDL (renameNamespace tMap dvpID) dl

instance PNamespace Axiom where
    propagateNspaces ns axiom =
        case axiom of
        Thing   -> Thing
        AxNothing -> AxNothing
        Class cID isdep modal annos descriptions ->
            Class (propagateNspaces ns cID)
                          isdep modal
                          (map (propagateNspaces ns) annos)
                          (map (propagateNspaces ns) descriptions)
        EnumeratedClass cID isdep annos indivIDs ->
            EnumeratedClass  (propagateNspaces ns cID)
                             isdep
                             (map (propagateNspaces ns) annos)
                             (map (propagateNspaces ns) indivIDs)
        DisjointClasses des1 des2 deses ->
            DisjointClasses (propagateNspaces ns des1)
                                (propagateNspaces ns des2)
                                (map (propagateNspaces ns) deses)
        EquivalentClasses des deses ->
            EquivalentClasses (propagateNspaces ns des)
                                  (map (propagateNspaces ns) deses)
        SubClassOf des1 des2 ->
            SubClassOf (propagateNspaces ns des1)
                           (propagateNspaces ns des2)
        Datatype dtID isdep annos ->
            Datatype (propagateNspaces ns dtID)
                     isdep
                     (map (propagateNspaces ns) annos)
        DatatypeProperty dvpID isdep annos dvpIDs isFunc descs drs ->
            DatatypeProperty (propagateNspaces ns dvpID)
                             isdep
                             (map (propagateNspaces ns) annos)
                             (map (propagateNspaces ns) dvpIDs)
                             isFunc
                             (map (propagateNspaces ns) descs)
                             (map (propagateNspaces ns) drs)
        ObjectProperty ivpID isdep annos ivpIDs maybeIvpID isSym
                       maybeFunc descs1 descs2 ->
            ObjectProperty (propagateNspaces ns ivpID)
                           isdep
                           (map (propagateNspaces ns) annos)
                           (map (propagateNspaces ns) ivpIDs)
                           (maybePropagate ns maybeIvpID)
                           isSym
                           maybeFunc
                           (map (propagateNspaces ns) descs1)
                           (map (propagateNspaces ns) descs2)
        AnnotationProperty apID annos ->
            AnnotationProperty (propagateNspaces ns apID)
                                   (map (propagateNspaces ns) annos)
        OntologyProperty opID annos ->
            OntologyProperty (propagateNspaces ns opID)
                                 (map (propagateNspaces ns) annos)
        DEquivalentProperties dvpID1 dvpID2 dvpIDs ->
            DEquivalentProperties (propagateNspaces ns dvpID1)
                                      (propagateNspaces ns dvpID2)
                                      (map (propagateNspaces ns) dvpIDs)
        DSubPropertyOf dvpID1 dvpID2 ->
            DSubPropertyOf (propagateNspaces ns dvpID1)
                               (propagateNspaces ns dvpID2)
        IEquivalentProperties ivpID1 ivpID2 ivpIDs ->
            IEquivalentProperties (propagateNspaces ns ivpID1)
                                      (propagateNspaces ns ivpID2)
                                      (map (propagateNspaces ns) ivpIDs)
        ISubPropertyOf ivpID1 ivpID2 ->
            ISubPropertyOf (propagateNspaces ns ivpID1)
                               (propagateNspaces ns ivpID2)

    renameNamespace tMap axiom =
        case axiom of
        Thing   -> Thing
        AxNothing -> AxNothing
        Class cID isdep modal annos descriptions ->
            Class (renameNamespace tMap cID)
                          isdep modal
                          (map (renameNamespace tMap) annos)
                          (map (renameNamespace tMap) descriptions)
        EnumeratedClass cID isdep annos indivIDs ->
            EnumeratedClass  (renameNamespace tMap cID)
                             isdep
                             (map (renameNamespace tMap) annos)
                             (map (renameNamespace tMap) indivIDs)
        DisjointClasses des1 des2 deses ->
            DisjointClasses (renameNamespace tMap des1)
                                (renameNamespace tMap des2)
                                (map (renameNamespace tMap) deses)
        EquivalentClasses des deses ->
            EquivalentClasses (renameNamespace tMap des)
                                  (map (renameNamespace tMap) deses)
        SubClassOf des1 des2 ->
            SubClassOf (renameNamespace tMap des1)
                           (renameNamespace tMap des2)
        Datatype dtID isdep annos ->
            Datatype (renameNamespace tMap dtID)
                     isdep
                     (map (renameNamespace tMap) annos)
        DatatypeProperty dvpID isdep annos dvpIDs isFunc descs drs ->
            DatatypeProperty (renameNamespace tMap dvpID)
                             isdep
                             (map (renameNamespace tMap) annos)
                             (map (renameNamespace tMap) dvpIDs)
                             isFunc
                             (map (renameNamespace tMap) descs)
                             (map (renameNamespace tMap) drs)
        ObjectProperty ivpID isdep annos ivpIDs maybeIvpID isSym
                       maybeFunc descs1 descs2 ->
            ObjectProperty (renameNamespace tMap ivpID)
                           isdep
                           (map (renameNamespace tMap) annos)
                           (map (renameNamespace tMap) ivpIDs)
                           (maybeRename tMap maybeIvpID)
                           isSym
                           maybeFunc
                           (map (renameNamespace tMap) descs1)
                           (map (renameNamespace tMap) descs2)
        AnnotationProperty apID annos ->
            AnnotationProperty (renameNamespace tMap apID)
                                   (map (renameNamespace tMap) annos)
        OntologyProperty opID annos ->
            OntologyProperty (renameNamespace tMap opID)
                                 (map (renameNamespace tMap) annos)
        DEquivalentProperties dvpID1 dvpID2 dvpIDs ->
            DEquivalentProperties (renameNamespace tMap dvpID1)
                                      (renameNamespace tMap dvpID2)
                                      (map (renameNamespace tMap) dvpIDs)
        DSubPropertyOf dvpID1 dvpID2 ->
            DSubPropertyOf (renameNamespace tMap dvpID1)
                               (renameNamespace tMap dvpID2)
        IEquivalentProperties ivpID1 ivpID2 ivpIDs ->
            IEquivalentProperties (renameNamespace tMap ivpID1)
                                      (renameNamespace tMap ivpID2)
                                      (map (renameNamespace tMap) ivpIDs)
        ISubPropertyOf ivpID1 ivpID2 ->
            ISubPropertyOf (renameNamespace tMap ivpID1)
                               (renameNamespace tMap ivpID2)

instance PNamespace DataLiteral where
    propagateNspaces ns dataL =
        case dataL of
        TypedL (lf, uri) -> TypedL (lf, (propagateNspaces ns uri))
        u                -> u
    renameNamespace tMap dataL =
        case dataL of
        TypedL (lf, uri) -> TypedL (lf, (renameNamespace tMap uri))
        u                -> u

instance PNamespace Description where
    propagateNspaces ns desc =
        case desc of
        DC cID          -> DC (propagateNspaces ns cID)
        DR restr        -> DR (propagateNspaces ns restr)
        UnionOf descs   -> UnionOf (map (propagateNspaces ns) descs)
        IntersectionOf descs  ->
            IntersectionOf (map (propagateNspaces ns) descs)
        ComplementOf desc1 -> ComplementOf (propagateNspaces ns desc1)
        OneOfDes indivIDs -> OneOfDes (map (propagateNspaces ns) indivIDs)

    renameNamespace tMap desc =
        case desc of
        DC cID          -> DC (renameNamespace tMap cID)
        DR restr        -> DR (renameNamespace tMap restr)
        UnionOf descs   -> UnionOf (map (renameNamespace tMap) descs)
        IntersectionOf descs  ->
            IntersectionOf (map (renameNamespace tMap) descs)
        ComplementOf desc1 -> ComplementOf (renameNamespace tMap desc1)
        OneOfDes indivIDs -> OneOfDes (map (renameNamespace tMap) indivIDs)

instance PNamespace Restriction where
    propagateNspaces ns restr =
        case restr of
        DataRestriction dvpID comp comps ->
            DataRestriction (propagateNspaces ns dvpID)
                            (propagateNspaces ns comp)
                            (map (propagateNspaces ns) comps)
        IndivRestriction ivpID comp comps ->
            IndivRestriction (propagateNspaces ns ivpID)
                             (propagateNspaces ns comp)
                             (map (propagateNspaces ns) comps)

    renameNamespace tMap restr =
        case restr of
        DataRestriction dvpID comp comps ->
            DataRestriction (renameNamespace tMap dvpID)
                            (renameNamespace tMap comp)
                            (map (renameNamespace tMap) comps)
        IndivRestriction ivpID comp comps ->
            IndivRestriction (renameNamespace tMap ivpID)
                             (renameNamespace tMap comp)
                             (map (renameNamespace tMap) comps)

instance PNamespace Drcomponent where
    propagateNspaces ns drComp =
        case drComp of
        DRCAllValuesFrom dr  -> DRCAllValuesFrom (propagateNspaces ns dr)
        DRCSomeValuesFrom dr -> DRCSomeValuesFrom (propagateNspaces ns dr)
        DRCValue dataLiteral -> DRCValue (propagateNspaces ns dataLiteral)
        u                    -> u

    renameNamespace tMap drComp =
        case drComp of
        DRCAllValuesFrom dr  -> DRCAllValuesFrom (renameNamespace tMap dr)
        DRCSomeValuesFrom dr -> DRCSomeValuesFrom (renameNamespace tMap dr)
        DRCValue dataLiteral -> DRCValue (renameNamespace tMap dataLiteral)
        u                    -> u

instance PNamespace Ircomponent where
    propagateNspaces ns irComp =
        case irComp of
        IRCAllValuesFrom desc  -> IRCAllValuesFrom (propagateNspaces ns desc)
        IRCSomeValuesFrom desc -> IRCSomeValuesFrom (propagateNspaces ns desc)
        IRCValue individualID  -> IRCValue (propagateNspaces ns individualID)
        u                      -> u

    renameNamespace tMap irComp =
        case irComp of
        IRCAllValuesFrom desc  -> IRCAllValuesFrom (renameNamespace tMap desc)
        IRCSomeValuesFrom desc -> IRCSomeValuesFrom (renameNamespace tMap desc)
        IRCValue individualID  -> IRCValue (renameNamespace tMap individualID)
        u                      -> u

instance PNamespace DataRange where
    propagateNspaces ns dr =
        case dr of
        DID dtID -> DID (propagateNspaces ns dtID)
        u        -> u

    renameNamespace tMap dr =
        case dr of
        DID dtID -> DID (renameNamespace tMap dtID)
        u        -> u

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

instance PNamespace SignAxiom where
   propagateNspaces _ signAxiom = signAxiom

   renameNamespace tMap signAxiom =
       case signAxiom of
       Subconcept cId1 cId2 -> Subconcept (renameNamespace tMap cId1)
                                          (renameNamespace tMap cId2)
       RoleDomain id1 rDomains -> RoleDomain (renameNamespace tMap id1)
                                      (map (renameNamespace tMap) rDomains)
       RoleRange id1 rRange -> RoleRange (renameNamespace tMap id1)
                                      (map (renameNamespace tMap) rRange)
       FuncRole (t, id1) -> FuncRole (t, (renameNamespace tMap id1))
       Conceptmembership iId des ->
           Conceptmembership (renameNamespace tMap iId)
                             (renameNamespace tMap des)

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

instance PNamespace RDomain where
    propagateNspaces _ rd = rd
    renameNamespace tMap rd =
        case rd of
        RDomain des -> RDomain (renameNamespace tMap des)

instance PNamespace OS11.RDomain where
    propagateNspaces _ rd = rd
    renameNamespace tMap rd =
        case rd of
        OS11.RDomain des -> OS11.RDomain (renameNamespace tMap des)
        OS11.DDomain des -> OS11.DDomain (renameNamespace tMap des)

instance PNamespace RRange where
   propagateNspaces _ rr = rr

   renameNamespace tMap rr =
        case rr of
        RIRange des -> RIRange (renameNamespace tMap des)
        RDRange dr  -> RDRange (renameNamespace tMap dr)

instance PNamespace OS11.RRange where
   propagateNspaces _ rr = rr

   renameNamespace tMap rr =
        case rr of
        OS11.RIRange des -> OS11.RIRange (renameNamespace tMap des)
        OS11.RDRange dr  -> OS11.RDRange (renameNamespace tMap dr)


instance PNamespace Sentence where
   propagateNspaces _ sent = sent

   renameNamespace tMap sent =
       case sent of
       OWLAxiom axiom -> OWLAxiom (renameNamespace tMap axiom)
       OWLFact fact   -> OWLFact  (renameNamespace tMap fact)

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

instance PNamespace FFS.OntologyFile where
    propagateNspaces ns (FFS.OntologyFile namespace ontology) =
        FFS.OntologyFile (propagateNspaces ns namespace)
                         (propagateNspaces ns ontology)
    renameNamespace tMap (FFS.OntologyFile namespace ontology) =
        FFS.OntologyFile (renameNamespace tMap namespace)
                         (renameNamespace tMap ontology)

instance PNamespace FFS.Ontology where
    propagateNspaces ns (FFS.Ontology uri importsList annosList axiomsList) =
        FFS.Ontology (propagateNspaces ns uri)
                     (map (propagateNspaces ns) importsList)
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) axiomsList)
    renameNamespace tMap (FFS.Ontology uri importsList annosList axiomsList) =
        FFS.Ontology (renameNamespace tMap uri)
                     (map (renameNamespace tMap) importsList)
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) axiomsList)

instance PNamespace FFS.Annotation where
    propagateNspaces ns anno =
        case anno of
          FFS.ExplicitAnnotation annoUri constant ->
              FFS.ExplicitAnnotation (propagateNspaces ns annoUri)
                                     (propagateNspaces ns constant)
          FFS.Label constant ->
              FFS.Label (propagateNspaces ns constant)
          FFS.Comment constant ->
              FFS.Comment (propagateNspaces ns constant)
          FFS.Annotation annoUri entity ->
              FFS.Annotation (propagateNspaces ns annoUri)
                             (propagateNspaces ns entity)
    renameNamespace tMap anno =
        case anno of
          FFS.ExplicitAnnotation annoUri constant ->
              FFS.ExplicitAnnotation (renameNamespace tMap annoUri)
                                     (renameNamespace tMap constant)
          FFS.Label constant ->
              FFS.Label (renameNamespace tMap constant)
          FFS.Comment constant ->
              FFS.Comment (renameNamespace tMap constant)
          FFS.Annotation annoUri entity ->
              FFS.Annotation (renameNamespace tMap annoUri)
                             (renameNamespace tMap entity)


instance PNamespace FFS.Axiom where
    propagateNspaces ns axiom =
        case axiom of
          FFS.SubClassOf annosList sub sup ->
              FFS.SubClassOf (map (propagateNspaces ns) annosList)
                             (propagateNspaces ns sub)
                             (propagateNspaces ns sup)
          FFS.EquivalentClasses annosList descList ->
              FFS.EquivalentClasses (map (propagateNspaces ns) annosList)
                                    (map (propagateNspaces ns) descList)
          FFS.DisjointClasses annosList descList ->
              FFS.DisjointClasses (map (propagateNspaces ns) annosList)
                                  (map (propagateNspaces ns) descList)
          FFS.DisjointUnion annosList classUri descList ->
              FFS.DisjointUnion (map (propagateNspaces ns) annosList)
                                (propagateNspaces ns classUri)
                                (map (propagateNspaces ns) descList)
          FFS.SubObjectPropertyOf annosList subExp objExp ->
              FFS.SubObjectPropertyOf (map (propagateNspaces ns) annosList)
                                      (propagateNspaces ns subExp)
                                      (propagateNspaces ns objExp)
          FFS.EquivalentObjectProperties annosList objExpList ->
              FFS.EquivalentObjectProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) objExpList)
          FFS.DisjointObjectProperties annosList objExpList ->
              FFS.DisjointObjectProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) objExpList)
          FFS.ObjectPropertyDomain annosList objExp desc ->
              FFS.ObjectPropertyDomain (map (propagateNspaces ns) annosList)
                                       (propagateNspaces ns objExp)
                                       (propagateNspaces ns desc)
          FFS.ObjectPropertyRange annosList objExp desc ->
              FFS.ObjectPropertyRange (map (propagateNspaces ns) annosList)
                                      (propagateNspaces ns objExp)
                                      (propagateNspaces ns desc)
          FFS.InverseObjectProperties annosList objExp1 objExp2 ->
              FFS.InverseObjectProperties (map (propagateNspaces ns) annosList)
                                          (propagateNspaces ns objExp1)
                                          (propagateNspaces ns objExp2)
          FFS.FunctionalObjectProperty annosList objExp ->
              FFS.FunctionalObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          FFS.InverseFunctionalObjectProperty annosList objExp ->
              FFS.InverseFunctionalObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          FFS.ReflexiveObjectProperty annosList objExp ->
              FFS.ReflexiveObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          FFS.IrreflexiveObjectProperty annosList objExp ->
              FFS.IrreflexiveObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          FFS.SymmetricObjectProperty  annosList objExp ->
              FFS.SymmetricObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          FFS.AntisymmetricObjectProperty  annosList objExp ->
              FFS.AntisymmetricObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          FFS.TransitiveObjectProperty annosList objExp ->
              FFS.TransitiveObjectProperty
                  (map (propagateNspaces ns) annosList)
                  (propagateNspaces ns objExp)
          FFS.SubDataPropertyOf annosList dpExp1 dpExp2 ->
              FFS.SubDataPropertyOf (map (propagateNspaces ns) annosList)
                                    (propagateNspaces ns dpExp1)
                                    (propagateNspaces ns dpExp2)
          FFS.EquivalentDataProperties annosList dpExpList ->
              FFS.EquivalentDataProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) dpExpList)
          FFS.DisjointDataProperties annosList  dpExpList ->
              FFS.DisjointDataProperties
                     (map (propagateNspaces ns) annosList)
                     (map (propagateNspaces ns) dpExpList)
          FFS.DataPropertyDomain annosList dpExp desc ->
              FFS.DataPropertyDomain (map (propagateNspaces ns) annosList)
                                     (propagateNspaces ns dpExp)
                                     (propagateNspaces ns desc)
          FFS.DataPropertyRange annosList dpExp dataRange ->
              FFS.DataPropertyRange (map (propagateNspaces ns) annosList)
                                     (propagateNspaces ns dpExp)
                                     (propagateNspaces ns dataRange)
          FFS.FunctionalDataProperty annosList dpExp ->
              FFS.FunctionalDataProperty (map (propagateNspaces ns) annosList)
                                         (propagateNspaces ns dpExp)
          FFS.SameIndividual annosList indUriList ->
              FFS.SameIndividual (map (propagateNspaces ns) annosList)
                                 (map (propagateNspaces ns) indUriList)
          FFS.DifferentIndividuals annosList indUriList ->
              FFS.DifferentIndividuals  (map (propagateNspaces ns) annosList)
                                        (map (propagateNspaces ns) indUriList)
          FFS.ClassAssertion annosList indUri desc ->
              FFS.ClassAssertion (map (propagateNspaces ns) annosList)
                                 (propagateNspaces ns indUri)
                                 (propagateNspaces ns desc)
          FFS.ObjectPropertyAssertion annosList objExp source target ->
             FFS.ObjectPropertyAssertion (map (propagateNspaces ns) annosList)
                                         (propagateNspaces ns objExp)
                                         (propagateNspaces ns source)
                                         (propagateNspaces ns target)
          FFS.NegativeObjectPropertyAssertion annosList objExp source target ->
             FFS.NegativeObjectPropertyAssertion
                    (map (propagateNspaces ns) annosList)
                    (propagateNspaces ns objExp)
                    (propagateNspaces ns source)
                    (propagateNspaces ns target)
          FFS.DataPropertyAssertion annosList dpExp source target ->
              FFS.DataPropertyAssertion
                 (map (propagateNspaces ns) annosList)
                 (propagateNspaces ns dpExp)
                 (propagateNspaces ns source)
                 (propagateNspaces ns target)
          FFS.NegativeDataPropertyAssertion annosList dpExp source target ->
              FFS.NegativeDataPropertyAssertion
                 (map (propagateNspaces ns) annosList)
                 (propagateNspaces ns dpExp)
                 (propagateNspaces ns source)
                 (propagateNspaces ns target)
          FFS.Declaration annosList entity ->
              FFS.Declaration (map (propagateNspaces ns) annosList)
                              (propagateNspaces ns entity)
          FFS.EntityAnno entityAnnotation  ->
              FFS.EntityAnno (propagateNspaces ns entityAnnotation)

    renameNamespace tMap axiom =
        case axiom of
          FFS.SubClassOf annosList sub sup ->
              FFS.SubClassOf (map (renameNamespace tMap) annosList)
                             (renameNamespace tMap sub)
                             (renameNamespace tMap sup)
          FFS.EquivalentClasses annosList descList ->
              FFS.EquivalentClasses (map (renameNamespace tMap) annosList)
                                    (map (renameNamespace tMap) descList)
          FFS.DisjointClasses annosList descList ->
              FFS.DisjointClasses (map (renameNamespace tMap) annosList)
                                  (map (renameNamespace tMap) descList)
          FFS.DisjointUnion annosList classUri descList ->
              FFS.DisjointUnion (map (renameNamespace tMap) annosList)
                                (renameNamespace tMap classUri)
                                (map (renameNamespace tMap) descList)
          FFS.SubObjectPropertyOf annosList subExp objExp ->
              FFS.SubObjectPropertyOf (map (renameNamespace tMap) annosList)
                                      (renameNamespace tMap subExp)
                                      (renameNamespace tMap objExp)
          FFS.EquivalentObjectProperties annosList objExpList ->
              FFS.EquivalentObjectProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) objExpList)
          FFS.DisjointObjectProperties annosList objExpList ->
              FFS.DisjointObjectProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) objExpList)
          FFS.ObjectPropertyDomain annosList objExp desc ->
              FFS.ObjectPropertyDomain (map (renameNamespace tMap) annosList)
                                       (renameNamespace tMap objExp)
                                       (renameNamespace tMap desc)
          FFS.ObjectPropertyRange annosList objExp desc ->
              FFS.ObjectPropertyRange (map (renameNamespace tMap) annosList)
                                      (renameNamespace tMap objExp)
                                      (renameNamespace tMap desc)
          FFS.InverseObjectProperties annosList objExp1 objExp2 ->
              FFS.InverseObjectProperties
                     (map (renameNamespace tMap) annosList)
                     (renameNamespace tMap objExp1)
                     (renameNamespace tMap objExp2)
          FFS.FunctionalObjectProperty annosList objExp ->
              FFS.FunctionalObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          FFS.InverseFunctionalObjectProperty annosList objExp ->
              FFS.InverseFunctionalObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          FFS.ReflexiveObjectProperty annosList objExp ->
              FFS.ReflexiveObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          FFS.IrreflexiveObjectProperty annosList objExp ->
              FFS.IrreflexiveObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          FFS.SymmetricObjectProperty  annosList objExp ->
              FFS.SymmetricObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          FFS.AntisymmetricObjectProperty  annosList objExp ->
              FFS.AntisymmetricObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          FFS.TransitiveObjectProperty annosList objExp ->
              FFS.TransitiveObjectProperty
                  (map (renameNamespace tMap) annosList)
                  (renameNamespace tMap objExp)
          FFS.SubDataPropertyOf annosList dpExp1 dpExp2 ->
              FFS.SubDataPropertyOf (map (renameNamespace tMap) annosList)
                                    (renameNamespace tMap dpExp1)
                                    (renameNamespace tMap dpExp2)
          FFS.EquivalentDataProperties annosList dpExpList ->
              FFS.EquivalentDataProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) dpExpList)
          FFS.DisjointDataProperties annosList  dpExpList ->
              FFS.DisjointDataProperties
                     (map (renameNamespace tMap) annosList)
                     (map (renameNamespace tMap) dpExpList)
          FFS.DataPropertyDomain annosList dpExp desc ->
              FFS.DataPropertyDomain (map (renameNamespace tMap) annosList)
                                     (renameNamespace tMap dpExp)
                                     (renameNamespace tMap desc)
          FFS.DataPropertyRange annosList dpExp dataRange ->
              FFS.DataPropertyRange (map (renameNamespace tMap) annosList)
                                     (renameNamespace tMap dpExp)
                                     (renameNamespace tMap dataRange)
          FFS.FunctionalDataProperty annosList dpExp ->
              FFS.FunctionalDataProperty (map (renameNamespace tMap) annosList)
                                         (renameNamespace tMap dpExp)
          FFS.SameIndividual annosList indUriList ->
              FFS.SameIndividual (map (renameNamespace tMap) annosList)
                                 (map (renameNamespace tMap) indUriList)
          FFS.DifferentIndividuals annosList indUriList ->
              FFS.DifferentIndividuals  (map (renameNamespace tMap) annosList)
                                        (map (renameNamespace tMap) indUriList)
          FFS.ClassAssertion annosList indUri desc ->
              FFS.ClassAssertion (map (renameNamespace tMap) annosList)
                                 (renameNamespace tMap indUri)
                                 (renameNamespace tMap desc)
          FFS.ObjectPropertyAssertion annosList objExp source target ->
             FFS.ObjectPropertyAssertion (map (renameNamespace tMap) annosList)
                                         (renameNamespace tMap objExp)
                                         (renameNamespace tMap source)
                                         (renameNamespace tMap target)
          FFS.NegativeObjectPropertyAssertion annosList objExp source target ->
             FFS.NegativeObjectPropertyAssertion
                    (map (renameNamespace tMap) annosList)
                    (renameNamespace tMap objExp)
                    (renameNamespace tMap source)
                    (renameNamespace tMap target)
          FFS.DataPropertyAssertion annosList dpExp source target ->
              FFS.DataPropertyAssertion
                 (map (renameNamespace tMap) annosList)
                 (renameNamespace tMap dpExp)
                 (renameNamespace tMap source)
                 (renameNamespace tMap target)
          FFS.NegativeDataPropertyAssertion annosList dpExp source target ->
              FFS.NegativeDataPropertyAssertion
                 (map (renameNamespace tMap) annosList)
                 (renameNamespace tMap dpExp)
                 (renameNamespace tMap source)
                 (renameNamespace tMap target)
          FFS.Declaration annosList entity ->
              FFS.Declaration (map (renameNamespace tMap) annosList)
                              (renameNamespace tMap entity)
          FFS.EntityAnno entityAnnotation  ->
              FFS.EntityAnno (renameNamespace tMap entityAnnotation)

instance PNamespace FFS.Entity where
    propagateNspaces ns entity =
        case entity of
          FFS.Datatype uri ->
              FFS.Datatype (propagateNspaces ns uri)
          FFS.OWLClassEntity uri ->
              FFS.OWLClassEntity (propagateNspaces ns uri)
          FFS.ObjectProperty uri ->
              FFS.ObjectProperty (propagateNspaces ns uri)
          FFS.DataProperty uri ->
              FFS.DataProperty (propagateNspaces ns uri)
          FFS.Individual uri ->
              FFS.Individual (propagateNspaces ns uri)
    renameNamespace tMap entity =
        case entity of
          FFS.Datatype uri ->
              FFS.Datatype (renameNamespace tMap uri)
          FFS.OWLClassEntity uri ->
              FFS.OWLClassEntity (renameNamespace tMap uri)
          FFS.ObjectProperty uri ->
              FFS.ObjectProperty (renameNamespace tMap uri)
          FFS.DataProperty uri ->
              FFS.DataProperty (renameNamespace tMap uri)
          FFS.Individual uri ->
              FFS.Individual (renameNamespace tMap uri)

instance PNamespace FFS.Constant where
    propagateNspaces ns constant =
        case constant of
          FFS.TypedConstant (l, uri) ->
              FFS.TypedConstant (l, (propagateNspaces ns uri))
          u -> u        -- for untyped constant
    renameNamespace tMap constant =
        case constant of
          FFS.TypedConstant (l, uri) ->
              FFS.TypedConstant (l, (renameNamespace tMap uri))
          u -> u        -- for untyped constant

instance PNamespace FFS.ObjectPropertyExpression where
    propagateNspaces ns opExp =
        case opExp of
          FFS.OpURI uri -> FFS.OpURI (propagateNspaces ns uri)
          FFS.InverseOp invOp -> FFS.InverseOp (propagateNspaces ns invOp)
    renameNamespace tMap opExp =
        case opExp of
          FFS.OpURI uri -> FFS.OpURI (renameNamespace tMap uri)
          FFS.InverseOp invOp -> FFS.InverseOp (renameNamespace tMap invOp)

instance PNamespace FFS.DataRange where
    propagateNspaces ns dr =
        case dr of
          FFS.DRDatatype uri ->
              FFS.DRDatatype (propagateNspaces ns uri)
          FFS.DataComplementOf dataRange ->
              FFS.DataComplementOf (propagateNspaces ns dataRange)
          FFS.DataOneOf constList ->
              FFS.DataOneOf (map (propagateNspaces ns) constList)
          FFS.DatatypeRestriction dataRange restrList ->
              FFS.DatatypeRestriction (propagateNspaces ns dataRange)
                                      (map pnRest restrList)
     where pnRest (facet, value) =
               (facet, propagateNspaces ns value)
    renameNamespace tMap dr =
        case dr of
          FFS.DRDatatype uri ->
              FFS.DRDatatype (renameNamespace tMap uri)
          FFS.DataComplementOf dataRange ->
              FFS.DataComplementOf (renameNamespace tMap dataRange)
          FFS.DataOneOf constList ->
              FFS.DataOneOf (map (renameNamespace tMap) constList)
          FFS.DatatypeRestriction dataRange restrList ->
              FFS.DatatypeRestriction (renameNamespace tMap dataRange)
                                      (map rnRest restrList)
     where rnRest (facet, value) =
               (facet, renameNamespace tMap value)

instance PNamespace FFS.Description where
    propagateNspaces ns desc =
        case desc of
          FFS.OWLClass uri ->
              FFS.OWLClass (propagateNspaces ns uri)
          FFS.ObjectUnionOf descList ->
              FFS.ObjectUnionOf (map (propagateNspaces ns) descList)
          FFS.ObjectIntersectionOf descList ->
              FFS.ObjectIntersectionOf (map (propagateNspaces ns) descList)
          FFS.ObjectComplementOf desc' ->
              FFS.ObjectComplementOf  (propagateNspaces ns desc')
          FFS.ObjectOneOf indsList ->
              FFS.ObjectOneOf (map (propagateNspaces ns) indsList)
          FFS.ObjectAllValuesFrom opExp desc' ->
              FFS.ObjectAllValuesFrom (propagateNspaces ns opExp)
                                      (propagateNspaces ns desc')
          FFS.ObjectSomeValuesFrom opExp desc' ->
              FFS.ObjectSomeValuesFrom (propagateNspaces ns opExp)
                                       (propagateNspaces ns desc')
          FFS.ObjectExistsSelf opExp ->
              FFS.ObjectExistsSelf (propagateNspaces ns opExp)
          FFS.ObjectHasValue opExp indUri ->
              FFS.ObjectHasValue (propagateNspaces ns opExp)
                                 (propagateNspaces ns indUri)
          FFS.ObjectMinCardinality card opExp maybeDesc ->
              FFS.ObjectMinCardinality card (propagateNspaces ns opExp)
                                       (maybePropagate ns maybeDesc)
          FFS.ObjectMaxCardinality card opExp maybeDesc ->
              FFS.ObjectMaxCardinality card (propagateNspaces ns opExp)
                                       (maybePropagate ns maybeDesc)
          FFS.ObjectExactCardinality card opExp maybeDesc ->
              FFS.ObjectExactCardinality card (propagateNspaces ns opExp)
                                         (maybePropagate ns maybeDesc)
          FFS.DataAllValuesFrom dpExp dpExpList dataRange ->
              FFS.DataAllValuesFrom (propagateNspaces ns dpExp)
                                    (map (propagateNspaces ns) dpExpList)
                                    (propagateNspaces ns dataRange)
          FFS.DataSomeValuesFrom dpExp dpExpList dataRange ->
              FFS.DataSomeValuesFrom  (propagateNspaces ns dpExp)
                                      (map (propagateNspaces ns) dpExpList)
                                      (propagateNspaces ns dataRange)
          FFS.DataHasValue dpExp const' ->
              FFS.DataHasValue (propagateNspaces ns dpExp)
                               (propagateNspaces ns const')
          FFS.DataMinCardinality  card dpExp maybeRange ->
              FFS.DataMinCardinality card (propagateNspaces ns dpExp)
                                     (maybePropagate ns maybeRange)
          FFS.DataMaxCardinality card dpExp maybeRange ->
              FFS.DataMaxCardinality  card (propagateNspaces ns dpExp)
                                     (maybePropagate ns maybeRange)
          FFS.DataExactCardinality card dpExp maybeRange ->
              FFS.DataExactCardinality card (propagateNspaces ns dpExp)
                                       (maybePropagate ns maybeRange)

    renameNamespace tMap desc =
        case desc of
          FFS.OWLClass uri ->
              FFS.OWLClass (renameNamespace tMap uri)
          FFS.ObjectUnionOf descList ->
              FFS.ObjectUnionOf (map (renameNamespace tMap) descList)
          FFS.ObjectIntersectionOf descList ->
              FFS.ObjectIntersectionOf (map (renameNamespace tMap) descList)
          FFS.ObjectComplementOf desc' ->
              FFS.ObjectComplementOf  (renameNamespace tMap desc')
          FFS.ObjectOneOf indsList ->
              FFS.ObjectOneOf (map (renameNamespace tMap) indsList)
          FFS.ObjectAllValuesFrom opExp desc' ->
              FFS.ObjectAllValuesFrom (renameNamespace tMap opExp)
                                      (renameNamespace tMap desc')
          FFS.ObjectSomeValuesFrom opExp desc' ->
              FFS.ObjectSomeValuesFrom (renameNamespace tMap opExp)
                                       (renameNamespace tMap desc')
          FFS.ObjectExistsSelf opExp ->
              FFS.ObjectExistsSelf (renameNamespace tMap opExp)
          FFS.ObjectHasValue opExp indUri ->
              FFS.ObjectHasValue (renameNamespace tMap opExp)
                                 (renameNamespace tMap indUri)
          FFS.ObjectMinCardinality card opExp maybeDesc ->
              FFS.ObjectMinCardinality card (renameNamespace tMap opExp)
                                       (maybeRename tMap maybeDesc)
          FFS.ObjectMaxCardinality card opExp maybeDesc ->
              FFS.ObjectMaxCardinality card (renameNamespace tMap opExp)
                                       (maybeRename tMap maybeDesc)
          FFS.ObjectExactCardinality card opExp maybeDesc ->
              FFS.ObjectExactCardinality card (renameNamespace tMap opExp)
                                         (maybeRename tMap maybeDesc)
          FFS.DataAllValuesFrom dpExp dpExpList dataRange ->
              FFS.DataAllValuesFrom (renameNamespace tMap dpExp)
                                    (map (renameNamespace tMap) dpExpList)
                                    (renameNamespace tMap dataRange)
          FFS.DataSomeValuesFrom dpExp dpExpList dataRange ->
              FFS.DataSomeValuesFrom  (renameNamespace tMap dpExp)
                                      (map (renameNamespace tMap) dpExpList)
                                      (renameNamespace tMap dataRange)
          FFS.DataHasValue dpExp const' ->
              FFS.DataHasValue (renameNamespace tMap dpExp)
                               (renameNamespace tMap const')
          FFS.DataMinCardinality  card dpExp maybeRange ->
              FFS.DataMinCardinality card (renameNamespace tMap dpExp)
                                     (maybeRename tMap maybeRange)
          FFS.DataMaxCardinality card dpExp maybeRange ->
              FFS.DataMaxCardinality  card (renameNamespace tMap dpExp)
                                     (maybeRename tMap maybeRange)
          FFS.DataExactCardinality card dpExp maybeRange ->
              FFS.DataExactCardinality card (renameNamespace tMap dpExp)
                                       (maybeRename tMap maybeRange)

instance PNamespace FFS.SubObjectPropertyExpression where
    propagateNspaces ns subOpExp =
        case subOpExp of
          FFS.OPExpression opExp ->
             FFS.OPExpression (propagateNspaces ns opExp)
          FFS.SubObjectPropertyChain opExpList ->
              FFS.SubObjectPropertyChain
                     (map (propagateNspaces ns) opExpList)
    renameNamespace tMap subOpExp =
        case subOpExp of
          FFS.OPExpression opExp ->
             FFS.OPExpression (renameNamespace tMap opExp)
          FFS.SubObjectPropertyChain opExpList ->
              FFS.SubObjectPropertyChain
                     (map (renameNamespace tMap) opExpList)

instance PNamespace FFS.EntityAnnotation where
    propagateNspaces ns (FFS.EntityAnnotation annoList1 entity annoList2) =
        FFS.EntityAnnotation (map (propagateNspaces ns) annoList1)
                             (propagateNspaces ns entity)
                             (map (propagateNspaces ns) annoList2)
    renameNamespace tMap (FFS.EntityAnnotation annoList1 entity annoList2) =
        FFS.EntityAnnotation (map (renameNamespace tMap) annoList1)
                             (renameNamespace tMap entity)
                             (map (renameNamespace tMap) annoList2)


-- propagate namespace of Maybe
maybePropagate :: (PNamespace a) => Namespace -> Maybe a -> Maybe a
maybePropagate ns obj =
    case obj of
             Just j -> Just (propagateNspaces ns j)
             Prelude.Nothing  -> Prelude.Nothing

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


integrateOntologyFile :: FFS.OntologyFile -> FFS.OntologyFile
                      -> FFS.OntologyFile
integrateOntologyFile of1@(FFS.OntologyFile ns1
                           (FFS.Ontology oid1 imp1 anno1 axiom1))
                      of2@(FFS.OntologyFile ns2
                           (FFS.Ontology oid2 imp2 anno2 axiom2)) =
  if of1 == of2 then of1
   else
    let (newNamespace, transMap) = integrateNamespaces ns1 ns2
    in  FFS.OntologyFile newNamespace
            (FFS.Ontology (newOid oid1 oid2)
                 (nub (imp1 ++ (map (renameNamespace transMap) imp2)))
                 (nub (anno1 ++ (map (renameNamespace transMap) anno2)))
                 (nub (axiom1 ++ (map (renameNamespace transMap) axiom2))))

    where newOid :: FFS.OntologyURI -> FFS.OntologyURI -> FFS.OntologyURI
          newOid id1 id2 =
              if id1 == id2 then id1
                 else id1 {localPart=
                           (uriToName $ localPart id1) ++
                             "_" ++
                             (uriToName $ uriToName $ localPart id2)}

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


