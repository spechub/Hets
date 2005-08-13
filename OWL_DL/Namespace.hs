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
-- import OWL_DL.Sign
import qualified Common.Lib.Map as Map
import Text.XML.HXT.DOM.XmlTreeTypes
import List(find)
import Maybe(fromJust)

type TranslationMap = Map.Map String String  -- ^ OldPrefix -> NewPrefix

-- propagate own namesapces from prefix to namespacesURI within a ontology
class PNamespace a where
    propagateNspaces :: Namespace -> a -> a
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
	if null nsUri then
	   if null pre then
	      let (pre', local') = span (/=':') 
				     (if (head local) == '\"' then
				         read local::String
				         else local
				     )
	      in if (length pre' > 2) || (null local') then
		    QN pre local nsUri
		    else let local'' = tail local'
		         in  prop pre' local''
	      else prop pre local
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
	OWL_DL.AS.Nothing -> OWL_DL.AS.Nothing
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
	OWL_DL.AS.Nothing -> OWL_DL.AS.Nothing
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
	u                    -> u

    renameNamespace tMap drComp =
	case drComp of
	DRCAllValuesFrom dr  -> DRCAllValuesFrom (renameNamespace tMap dr)
	DRCSomeValuesFrom dr -> DRCSomeValuesFrom (renameNamespace tMap dr)
	u                    -> u

instance PNamespace Ircomponent where
    propagateNspaces ns irComp =
	case irComp of
	IRCAllValuesFrom desc  -> IRCAllValuesFrom (propagateNspaces ns desc)
	IRCSomeValuesFrom desc -> IRCSomeValuesFrom (propagateNspaces ns desc)
	u                      -> u

    renameNamespace tMap irComp =
	case irComp of
	IRCAllValuesFrom desc  -> IRCAllValuesFrom (renameNamespace tMap desc)
	IRCSomeValuesFrom desc -> IRCSomeValuesFrom (renameNamespace tMap desc)
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

maybePropagate :: (PNamespace a) => Namespace -> Maybe a -> Maybe a
maybePropagate ns obj = 
    case obj of 
	     Just j -> Just (propagateNspaces ns j)
	     Prelude.Nothing  -> Prelude.Nothing

maybeRename :: (PNamespace a) => TranslationMap -> Maybe a -> Maybe a
maybeRename tMap obj =
    case obj of
	     Just j -> Just (renameNamespace tMap j)
	     Prelude.Nothing -> Prelude.Nothing

integrateNamespaces :: Namespace -> Namespace
                    -> (Namespace,TranslationMap)
integrateNamespaces oldNsMap testNsMap =
    testAndInteg oldNsMap (Map.toList testNsMap) Map.empty
  
   where testAndInteg :: Namespace -> [(String, String)] 
		      -> Map.Map String String
		      -> (Namespace, TranslationMap)
	 testAndInteg old [] tm = (old, tm)
 	 testAndInteg old ((pre, uri):r) tm 
             | pre `elem` (Map.keys old) && uri `elem` (Map.elems old) =
		 testAndInteg old r tm
             -- if the uri already existed in old map, the key muss be changed.
	     | uri `elem` (Map.elems old) = 
		 testAndInteg old r 
			  (Map.insert pre (findKey uri $ Map.toList old) tm)
	     | pre `elem` (Map.keys old) = 
	        let pre' = disambiguateName pre (Map.keys old)
                in  testAndInteg (Map.insert pre' uri old) r 
			(Map.insert pre pre' tm)
	     | otherwise = testAndInteg (Map.insert pre uri old) r tm

         findKey :: String -> [(String, String)] -> String
	 findKey ele [] = ele      -- remove warnung ...
	 findKey ele1 ((key,ele2):rest) 
	    | ele1 == ele2 = key
	    | otherwise = findKey ele1 rest
	     
         disambiguateName :: String -> [String] -> String
	 disambiguateName name nameSet =
	     fromJust $ find (not . flip elem nameSet) 
			  [name ++ (show (i::Int)) | i <-[1..]]

integrateOntology :: Ontology -> Ontology -> Ontology
integrateOntology (Ontology oid1 directives1 ns1) 
                  (Ontology oid2 directives2 ns2) =
    let (newNamespace, transMap) = integrateNamespaces ns1 ns2
    in  Ontology (newOid oid1 oid2) 
	         (directives1 ++ (map (renameNamespace transMap) directives2)) 
		 newNamespace
    where newOid :: Maybe OntologyID -> Maybe OntologyID -> Maybe OntologyID
	  newOid Prelude.Nothing Prelude.Nothing = Prelude.Nothing
	  newOid Prelude.Nothing oid@(Just _) = oid
	  newOid oid@(Just _) Prelude.Nothing = oid
	  newOid (Just id1) (Just id2) = 
	      Just (id1 { localPart=
			  (localPart id1) ++ "&" ++ (localPart id2)})