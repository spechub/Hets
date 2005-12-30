{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  portable

This module is OWL namespace handler.

-}


module OWL_DL.Namespace where

import OWL_DL.AS
import OWL_DL.Sign
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.AS_Annotation as Common.Annotation
import Text.XML.HXT.DOM.XmlTreeTypes
import List(find, nub)
import Maybe(fromJust)
import Char(isDigit, isAlpha)


type TranslationMap = Map.Map String String  -- ^ OldPrefix -> NewPrefix

-- propagate own namesapces from prefix to namespacesURI within a ontology
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

instance PNamespace RDomain where
    propagateNspaces _ rd = rd
    renameNamespace tMap rd = 
        case rd of
        RDomain des -> RDomain (renameNamespace tMap des)

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
    
    renameNamespace tMap (Common.Annotation.NamedSen str isAx isDef sent) =
        Common.Annotation.NamedSen str isAx isDef (renameNamespace tMap sent)

-- propagete namespace of Maybe
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


