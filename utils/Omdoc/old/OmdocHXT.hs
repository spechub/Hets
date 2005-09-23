module OmdocHXT where

import Text.XML.HXT.Parser

import Omdoc_HXTAccess

{- TODO
   - element-processing-structures
   - validation
-}


{-
   C L A S S E S
   These classes are used to define special functions on certain tagged xml-structures.
   When a OMDoc-document is read in it is parsed by the Haskell XML Toolbox and the resulting Xml-structures get tagged on-the-fly by abstract datatypes.
   These datatypes serve as interfaces to OMDoc by providing instances to classes with specialized functions.
   These functions are currently designed to extract further structures from the Xml until a datatype is reached that can be directly manipulated.
-}

{-
   XmlItem
   The XmlItem class is the basis for further classes. It makes sure that an instance can be converted to and from XmlTrees.
   The exact implementation is dependent to the instance but converting to and from should not change the meaning of the data.
   There are also functions for getting and setting attributes that have save defaults because they are perhaps not really needed.
-}
class XmlItem a where
	toXmlTrees::a->XmlTrees
	fromXmlTrees::XmlTrees->a
	getAttributeValue::String->a->String
	getAttributeValue _ _ = ""
	setAttributeValue::String->String->a->a
	setAttributeValue _ _ a = a

{-
   This class hase been made for structures like the dublin-core-role. It exists only as attributes to a Xml-structure and can be represented by a list of these attributes.
-}
class IsAttributeList a where
	fromAttributeList::XmlTrees->a
	toAttributeList::a->[(String, String)]

{-
   This class marks an XmlItem as having dublin-core-role information and provides default functions for getting and setting the information.
   See datatype-section for DCRole.
-}
class (XmlItem a)=>HasDCRole a where
	getDCRole::a->DCRole
	getDCRole a = fromAttributeList $ toXmlTrees a
	setDCRole::a->DCRole->a
	setDCRole a dcr =
		fromXmlTrees $
			setValueList (toAttributeList dcr) $
				toXmlTrees a

{-
   With this class a XmlItem gets marked as having textual content. The default funtions concatenate all text-elements in the item to form a string for returning or replace all elements by a single text element when setting.
   This class is meant for tags that contain no other elements than text.
-}
class (XmlItem a)=>HasTextContent a where
	getTextContent::a->String
	getTextContent a = xmlGetTextContent $ toXmlTrees a
	setTextContent::String->a->a
	setTextContent s a = fromXmlTrees $
		flip xmlSetTextContent s $ toXmlTrees a

{-
   This class marks an XmlItem as containing metadata-tags.
-}
class (XmlItem a)=>HasMetadata a where
	getMetadata::a->XmlTrees
	getMetadata a = applyXmlFilter
		(getChildren .> ismetadata)
		$ toXmlTrees a
	
{-
   With this class a XmlItem with metadata gets also tagged as having dublin-core-elements.
   See also datatypes for 'OmdocMetadata'.
-}
class (HasMetadata a)=>WithDublinCore a where
	getDCMItems::a->[DublinCoreMetadataItem]
	getDCMItems a = 
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter xmlGetDCItems $
			getMetadata a
			
{-
   This class marks an XmlItem as containing tags that belong to Open Math Objects.
-} 
class (XmlItem a)=>HasOMOBJItems a where
	getOMOBJItems::a->[OMOBJItem]
	getOMOBJItems a =
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter xmlGetOMOBJItems $
			toXmlTrees a

{-
   With this class a XmlItem gets tagged as having items belonging to CMP-tags.
-}
class (XmlItem a)=>HasCMPItems a where
	getCMPItems::a->[CMPItem]
	getCMPItems a = map (\t -> fromXmlTrees [t]) $
		applyXmlFilter xmlGetCMPItems $
		toXmlTrees a
		
{-
   This class tags a XmlItem as containing CMP-tags.
-}
class (XmlItem a)=>HasCMPs a where
	getCMPs::a->[CMP]
	getCMPs a = map (\t -> fromXmlTrees [t]) $
		applyXmlFilter (getChildren .> isCMP) $
			toXmlTrees a

{-
   This class tags a XmlItem as having items belonging to FMP-tags.
-}
class (XmlItem a)=>HasFMPItems a where
	getFMPItems::a->[FMPItem]
	getFMPItems a =
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter xmlGetFMPItems $
			toXmlTrees a

{-
   With this class a XmlItem gets tagged as containing FMP-tags.
-}
class (XmlItem a)=>HasFMPs a where
	getFMPs::a->[FMP]
	getFMPs a = 
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter isFMP $
			toXmlTrees a

{-
   This class marks an XmlItem as having items belonging into theories.
-}
class (XmlItem a)=>HasInTheoryItems a where
	getInTheoryItems::a->[InTheoryItem]
	getInTheoryItems a =
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter (getChildren .> xmlInTheoryItem) $
				toXmlTrees a
				
{-
   This class tags a XmlItem as having commonname-tags.
-}
class (XmlItem a)=>HasCommonNames a where
	getCommonNames::a->[CommonName]
	getCommonNames a = map (\t -> fromXmlTrees [t]) $
		applyXmlFilter (getChildren .> iscommonname) $
		toXmlTrees a 

{-
   D A T A T Y P E S
   These Datatypes are meant to tag Xml-structures so they are often cunstructed just by their name and the corresponding XmlTrees.
-}
		
-- OMDoc
data Omdoc = Omdoc {
	omdoc		:: XmlTrees -- omdoc-element
	}
	
-- Instance as XmlItem
instance XmlItem Omdoc where
	toXmlTrees o = omdoc o
	fromXmlTrees t = Omdoc t
	getAttributeValue a o = getValueString a (omdoc o)
	setAttributeValue a v o = Omdoc (setValueString a v (omdoc o))
	
-- Simple Show instance
instance Show Omdoc where
	show o = 
	   ("OMDoc-ID : " ++ getAttributeValue "id" o ++ "\n"
	   ++ "Metadata : " ++ ( case metadata o of
		[] -> "No";
		 _ -> "Yes"; ) ++ "\n"
	   ++ "Catalogue : " ++ ( case catalogue o of
		[] -> "No";
		 _ -> "Yes"; ) ++ "\n"
	   ++ "Number of Items : " ++ (show $ length $ items o ) )

-- Some convenient instances
instance HasMetadata Omdoc
instance WithDublinCore Omdoc
	
{- 
   Creates an Omdoc-Instance from XmlTrees
-}
mkOmdoc::XmlTrees->Omdoc
mkOmdoc t = Omdoc {
		omdoc = applyXmlFilter xmlGetOmdoc t -- strip root-node
		}

{-
   To write the OMDoc-Structure a Root-Node and a DOCTYPE-Element have to be inserted.
   Open Question : Where will the DTD be ? Absolute URI ? (currently "omdoc.dtd")
-}
writeableOmdoc::Omdoc->XmlTree
writeableOmdoc o =
		(NTree
			((\(NTree a _) -> a) emptyRoot)
			((NTree omdocDocTypeElem [])
				:(NTree (XText "\n")[])
				:(omdoc o)
			)
		)

{-
   This function extracts all (interresting) internal items from the omdoc.
-}
getOmdocItems::Omdoc->[OmdocItem]
getOmdocItems o =
	map (\t -> fromXmlTrees [t]) $ items o

-- Metadata
data OmdocMetadata = OmdocMetadata XmlTrees

-- Instance as having metadata
instance HasMetadata OmdocMetadata where
	getMetadata (OmdocMetadata m) = m
		
instance WithDublinCore OmdocMetadata

-- XmlItem instance
instance XmlItem OmdocMetadata where
	fromXmlTrees t = OmdocMetadata t
	toXmlTrees (OmdocMetadata m) = m

-- Dublin Core Role
defRoleString = "aut"
defRoleLang = "en"

-- perhaps validation should be made by HXT and not here...
validRoleString::String->Bool
validRoleString x
	| x=="aut" = True
	| x=="ant" = True
	| x=="clb" = True
	| x=="edt" = True
	| x=="ths" = True
	| x=="trc" = True
	| x=="trl" = True
	| otherwise = False
	
-- Dublin Core Role as datatype
data DCRole = DCRole {
	 rlang	:: String -- ISO639, def 'en', xml:lang - not validated right now
	,rrole	:: String
	,rid	:: String
	,rstyle	:: String
	}
	
-- Simple Show instance
instance Show DCRole where
	show (DCRole l r i s) =
		("Role-ID : " ++ i ++ "\n"
		 ++ "Type : " ++ r ++ "\n"
		 ++ "Style : " ++ s ++ "\n"
		 ++ "Language : " ++ l ++ "\n"
		 )
		 
-- This function creates a DCRole instance
-- (id, type, style, language)
mkDCRole::(String, String, String, String)->DCRole
mkDCRole (rid, rtp, rst, rln) = DCRole {
	 rlang = case rln of
	 	"" -> defRoleLang;
		 _ -> rln
	,rrole = case rtp of
		"" -> defRoleString;
		 _ -> if validRoleString rtp then rtp else (error "Invalid Role!")
	,rstyle = rst
	,rid = rid
	}

-- Instance as AttributeList	
instance IsAttributeList DCRole where
	fromAttributeList t = DCRole {
	 rlang = getValueString "xml:lang" t
	,rrole = getValueString "role" t
	,rid = getValueString "id" t
	,rstyle = getValueString "style" t
	}
	
	-- If not set do not emit implied values --
	toAttributeList (DCRole l r i s) =
	  	[ ("xml:lang", l) -- always set via default
		 ,("role", r)
		]
		 ++ (case i of "" -> []; _ -> [("id", i)])
		 ++ (case s of "" -> []; _ -> [("style", s)])

-- Dublin Core Metadata
data DublinCoreMetadataItem =
	  DCMContributor XmlTrees
	| DCMCreator XmlTrees
	| DCMTitle XmlTrees
	| DCMSubject XmlTrees
	| DCMDescription XmlTrees
	| DCMPublisher XmlTrees
	| DCMDate XmlTrees
	| DCMType XmlTrees
	| DCMFormat XmlTrees
	| DCMIdentifier XmlTrees
	| DCMSource XmlTrees
	| DCMLanguage XmlTrees
	| DCMRelation XmlTrees
	| DCMRights XmlTrees

-- Simple Show Instance
instance Show DublinCoreMetadataItem where
	show dcmi@(DCMContributor _) = show $
		"Contributor: " ++ getTextContent dcmi 
	show dcmi@(DCMCreator _) = show $
		"Creator: " ++ getTextContent dcmi 
	show dcmi@(DCMTitle _) = show $
		"Title: " ++ getTextContent dcmi 
	show dcmi@(DCMSubject _) = show $
		"Subject: " ++ getTextContent dcmi 
	show dcmi@(DCMDescription _) = show $
		"Description: " ++ getTextContent dcmi 
	show dcmi@(DCMPublisher _) = show $
		"Publisher: " ++ getTextContent dcmi 
	show dcmi@(DCMDate _) = show $
		"Date: " ++ getTextContent dcmi 
	show dcmi@(DCMType _) = show $
		"Type: " ++ getTextContent dcmi 
	show dcmi@(DCMFormat _) = show $
		"Format: " ++ getTextContent dcmi 
	show dcmi@(DCMIdentifier _) = show $
		"Identifier: " ++ getTextContent dcmi 
	show dcmi@(DCMSource _) = show $
		"Source: " ++ getTextContent dcmi 
	show dcmi@(DCMLanguage _) = show $
		"Language: " ++ getTextContent dcmi 
	show dcmi@(DCMRelation _) = show $
		"Relation: " ++ getTextContent dcmi 
	show dcmi@(DCMRights _) = show $
		"Rights: " ++ getTextContent dcmi 

-- Insatnce as XmlItem
instance XmlItem DublinCoreMetadataItem where
	fromXmlTrees (t:_) -- Only the first Element in the XmlTrees list is checked
		| (isTag "Creator" t) /= [] = DCMCreator [t]
		| (isTag "Contributor" t) /= [] = DCMContributor [t]
		| (isTag "Title" t) /= [] = DCMTitle [t]
		| (isTag "Subject" t) /= [] = DCMSubject [t]
		| (isTag "Description" t) /= [] = DCMDescription [t]
		| (isTag "Publisher" t) /= [] = DCMPublisher [t]
		| (isTag "Date" t) /= [] = DCMDate [t]
		| (isTag "Type" t) /= [] = DCMType [t]
		| (isTag "Format" t) /= [] = DCMFormat [t]
		| (isTag "Identifier" t) /= [] = DCMIdentifier [t]
		| (isTag "Source" t) /= [] = DCMSource [t]
		| (isTag "Language" t) /= [] = DCMLanguage [t]
		| (isTag "Relation" t) /= [] = DCMRelation [t]
		| (isTag "Rights" t) /= [] = DCMRights [t]
	toXmlTrees (DCMCreator t) = t
	toXmlTrees (DCMContributor t) = t
	toXmlTrees (DCMTitle t) = t
	toXmlTrees (DCMSubject t) = t
	toXmlTrees (DCMDescription t) = t
	toXmlTrees (DCMPublisher t) = t
	toXmlTrees (DCMDate t) = t
	toXmlTrees (DCMType t) = t
	toXmlTrees (DCMFormat t) = t
	toXmlTrees (DCMIdentifier t) = t
	toXmlTrees (DCMSource t) = t
	toXmlTrees (DCMLanguage t) = t
	toXmlTrees (DCMRelation t) = t
	toXmlTrees (DCMRights t) = t
	
-- Some Items have a DCRole
instance HasDCRole DublinCoreMetadataItem
			
-- Some Items have textual content
instance HasTextContent DublinCoreMetadataItem
			
-- This function creates a 'Creator'-Instance
mkDCMCreator::(String, String, String, String)->String->DublinCoreMetadataItem
mkDCMCreator dcroles content =
	DCMCreator (
		xtag "Creator"
		  (fromAttrl (toAttributeList (mkDCRole dcroles)))
		  (xtext content)
		)

-- This function creates a 'Contributor'-Instance
mkDCMContributor::(String, String, String, String)->String->DublinCoreMetadataItem
mkDCMContributor dcroles content =
	DCMContributor (
		xtag "Contributor"
		  (fromAttrl (toAttributeList (mkDCRole dcroles)))
		  (xtext content)
		)

-- This function creates metadata from Dublin-Core-Metadata
mkOmdocMetadata::[DublinCoreMetadataItem]->OmdocMetadata
mkOmdocMetadata l = OmdocMetadata (
	xtag "metadata"
	[]
	(concatMap toXmlTrees l)
	)
	
-- CMP

-- Datatype for CMP-tags
data CMP = CMP XmlTrees

-- Instance as XmlItem
instance XmlItem CMP where
	fromXmlTrees (t:_)
		| (isCMP t) /= [] = CMP [t]
	toXmlTrees (CMP t) = t
	
-- obvious
instance HasCMPItems CMP

-- CMPItems
	
-- Items in CMP as datatype
data CMPItem =
	  PCDATA XmlTrees
	| OMOBJ XmlTrees
	| Omlet XmlTrees
	| With XmlTrees
	| Ref XmlTrees
	| Ignore XmlTrees
	deriving Show

-- Instance as XmlItem
instance XmlItem CMPItem where
 	fromXmlTrees (t:_)
		| (isXText t) /= [] = PCDATA [t]
		| (isTag "OMOBJ" t) /= [] = OMOBJ [t]
		| (isTag "omlet" t) /= [] = Omlet [t]
		| (isTag "with" t) /= [] = With [t]
		| (isTag "ref" t) /= [] = Ref [t]
		| (isTag "ignore" t) /= [] = Ignore [t]
	toXmlTrees (PCDATA t) = t
	toXmlTrees (OMOBJ t) = t
	toXmlTrees (Omlet t) = t
	toXmlTrees (With t) = t
	toXmlTrees (Ref t) = t
	toXmlTrees (Ignore t) = t
	
-- Some DCItems have CMPItems
instance HasCMPItems DublinCoreMetadataItem

-- OMOBJ

-- Items in OMOBJ as datatype
data OMOBJItem = 
	  OMS XmlTrees
	| OMV XmlTrees
	| OMI XmlTrees
	| OMB XmlTrees
	| OMSTR XmlTrees
	| OMF XmlTrees
	| OMA XmlTrees
	| OMBIND XmlTrees
	| OME XmlTrees
	| OMATTR XmlTrees
	deriving Show
	
-- Instance as XmlItems
instance XmlItem OMOBJItem where
	fromXmlTrees (t:_)
		| (isOMS t) /= [] = OMS [t]
		| (isOMV t) /= [] = OMV [t]
		| (isOMI t) /= [] = OMI [t]
		| (isOMB t) /= [] = OMB [t]
		| (isOMSTR t) /= [] = OMSTR [t]
		| (isOMF t) /= [] = OMF [t]
		| (isOMA t) /= [] = OMA [t]
		| (isOMBIND t) /= [] = OMBIND [t]
		| (isOME t) /= [] = OME [t]
		| (isOMATTR t) /= [] = OMATTR [t]
	toXmlTrees (OMS t) = t
	toXmlTrees (OMV t) = t
	toXmlTrees (OMI t) = t
	toXmlTrees (OMB t) = t
	toXmlTrees (OMSTR t) = t
	toXmlTrees (OMF t) = t
	toXmlTrees (OMA t) = t
	toXmlTrees (OMBIND t) = t
	toXmlTrees (OME t) = t
	toXmlTrees (OMATTR t) = t
	
-- Some DCItems have OMOBJItems		
instance HasOMOBJItems DublinCoreMetadataItem

-- FMP

-- Datatype for FMP-tags
data FMP = FMP XmlTrees

--Instance as XmlItem
instance XmlItem FMP where
	fromXmlTrees (t:_)
		| (isFMP t) /= [] = FMP [t]
	toXmlTrees (FMP t) = t
	
-- obvious	
instance HasFMPItems FMP

-- Items in FMP as datatype
data FMPItem =
	  FMPAssumption XmlTrees
	| FMPConclusion XmlTrees
	| FMPOMOBJ XmlTrees
	
-- Instance as XmlItems
instance XmlItem FMPItem where
	fromXmlTrees (t:_)
		| (isassumption t) /= [] = FMPAssumption [t]
		| (isconclusion t) /= [] = FMPConclusion [t]
		| (isOMOBJ t) /= [] = FMPOMOBJ [t]
	toXmlTrees (FMPAssumption t) = t
	toXmlTrees (FMPConclusion t) = t
	toXmlTrees (FMPOMOBJ t) = t
	
-- OmdocCatalogue

-- Datatype
data OmdocCatalogue = OmdocCatalogue {
	odcatalogue :: XmlTrees
	}
	
-- Simple Show instance
instance Show OmdocCatalogue where
	show oc =
		show $ "Catalogue :\n" ++
			(concatMap (\n -> (show n)++"\n") $ getODCLocs oc)

-- Instance as XmlItem
instance XmlItem OmdocCatalogue where
	fromXmlTrees t = OmdocCatalogue t
	toXmlTrees o = odcatalogue o
	
-- Datatype for loc-tags -- direct representation
data ODCLoc = ODCLoc {
	 ltheory :: String
	,lomdoc :: String
	,lcd :: String
	}
	
-- Simple Show Instance
instance Show ODCLoc where
	show (ODCLoc t o c) =
		show $ "Theory: " ++ t ++ ", "
			++ "Omdoc: " ++ o ++ ", "
			++ "CD: " ++ c
	
-- This function creates a loc-element
mkODCLoc::(String, String, String)->ODCLoc
mkODCLoc (t, o, c) = ODCLoc t o c

-- Instance as XmlItem
instance XmlItem ODCLoc where
	fromXmlTrees t = ODCLoc {
		 ltheory = getValueString "theory" t
		,lomdoc = getValueString "omdoc" t
		,lcd = getValueString "cd" t
		}
	toXmlTrees l = xtag "loc" -- construct XmlTrees
		(fromAttrl [	 ("theory", (ltheory l))
				,("omdoc", (lomdoc l))
				,("cd", (lcd l))
			   ])
		[]

-- This Function extracts loc-elements from the catalogue
getODCLocs::OmdocCatalogue->[ODCLoc]
getODCLocs o = createLocs (applyXmlFilter (getChildren .> isloc) (odcatalogue o)) where
	createLocs [] = []
	createLocs (t:rest) = (fromXmlTrees [t]):(createLocs rest)
	
-- This function creates a catalogue from loc-elements
createODCatalogue::[ODCLoc]->OmdocCatalogue
createODCatalogue l = OmdocCatalogue (
	xtag "catalogue" (fromAttrl [])
		(concatMap toXmlTrees l)
		)
		
-- CommonName

-- Datatype
data CommonName = CommonName XmlTrees

-- Instance as XmlItem
instance XmlItem CommonName where
	fromXmlTrees (t:_)
		| (iscommonname t) /= [] = CommonName [t]
	toXmlTrees (CommonName t) = t
	
-- Can have CMPItems
instance HasCMPItems CommonName

-- Simple Show instance
instance Show CommonName where
	show (CommonName t) = show $
		(xmlGetTextContent t)
		++ " (" ++ (getValueString "xml:lang" t) ++ ")"
		
-- Theories

-- Datatype
data Theory = Theory XmlTrees

-- Simple Show instance
instance Show Theory where
	show (th@(Theory t)) =
		show $
		"Theory :\nid: " ++ (getValueString "id" t)
		++ "\nCommonNames : (" ++ (show $ getCommonNames th) ++ ")\n" 

-- Instance as XmlItem
instance XmlItem Theory where
	fromXmlTrees (t:_)
		| (istheory t) /= [] = Theory [t]
	toXmlTrees (Theory t) = t
	
-- This function extracts theories from an Omdoc-instance
getTheories::Omdoc->[Theory]
getTheories o =
	foldr (\n ts -> (case n of
		(OIInTheoryOmdocItem (ITOITheory t)) -> ((Theory t):ts)
		_	-> ts
		) ) [] (getOmdocItems o)
		
-- Theories contain some items...
instance HasMetadata Theory
instance WithDublinCore Theory
instance HasCommonNames Theory
instance HasCMPs Theory
instance HasInTheoryItems Theory

{-
   These functions extract certain items out of the omdoc-structure.
   Extracting them at parsetime is possible but makes keeping the
   structure consistent when writing it harder.
-}

-- concat all text elements to a string
xmlGetTextContent::XmlTrees->String
xmlGetTextContent t =
	concatMap (\(NTree (XText a) _) -> a) ((applyXmlFilter (getChildren .> isXText)) t)
	
-- replace all text elements by a new one
xmlSetTextContent::XmlTrees->String->XmlTrees
xmlSetTextContent t@((NTree n l):r) s =
	((NTree n ((NTree (XText s) []):oc)):r)	where
	  oc = applyXmlFilter (getChildren `notContaining` isXText) t

-- get the value of an attribute
getValueString::String->XmlTrees->String
getValueString a t = showXmlTreesNS $ getValue a (t!!0)

-- set the value of an attribute
setValueString::String->String->XmlTrees->XmlTrees
setValueString a v t = applyXmlFilter (addAttr a v) t

-- set a list of attributes
setValueList::[(String, String)]->XmlTrees->XmlTrees
setValueList l t = foldr (\(a, v) t' -> setValueString a v t') t l

-- get the id of an omdoc -- obsolete
getID::Omdoc->String
getID (Omdoc { omdoc=od }) = getValueString "id" od

-- set the id of an omdoc -- obsolete
setID::Omdoc->String->Omdoc
setID o i = Omdoc {-(rootnode o)-} (setValueString "id" i (omdoc o))

-- Create a OmdocMetadata-instance from an Omdoc-instance
getOmdocMetadata::Omdoc->OmdocMetadata
getOmdocMetadata o = OmdocMetadata $ metadata o

-- Create a OmdocCatalogue-instance from an Omdoc-instance
getOmdocCatalogue::Omdoc->OmdocCatalogue
getOmdocCatalogue o = OmdocCatalogue $ catalogue o

-- Extract the metadata-element from an Omdoc
metadata::Omdoc->XmlTrees
metadata (Omdoc { omdoc=od }) = applyXmlFilter xmlGetMetadata od

-- Extract the catalogue-element from an Omdoc
catalogue::Omdoc->XmlTrees
catalogue (Omdoc { omdoc=od }) = applyXmlFilter xmlGetCatalogue od

-- Extract all Omdoc-elements from an Omdoc
items::Omdoc->XmlTrees
items (Omdoc { omdoc=od }) = applyXmlFilter xmlGetOmdocItems od

{-
   R E A D I N G / W R I T I N G
   These functions read in or write OMDoc-documents
-}
		
{-
   Create an Omdoc from an URI - if possible.
   Returns 'IO Nothing' if any error/warning occures parsing
   the document.
-}
mkOmdocFromURI::String->IO Omdoc
mkOmdocFromURI f = do
	doc <- run' $ parseDocument
		[(a_source, f), (a_issue_errors, v_0)]
		emptyRoot
	return	(
		if validXml doc then
			mkOmdoc doc
			else
			(error ("Not a valid OMDoc : \"" ++ f ++ "\""))
	        )

{-
   This function creates a new Omdoc from Attributes, Metadata, a Catalogue and OmdocItems
   Currently hardly tested because there are no functions to create OmdocItems...
-}
createOmdoc::Attributes->(Maybe OmdocMetadata)->(Maybe OmdocCatalogue)->[OmdocItem]->Omdoc
createOmdoc oattr mom moc items =  mkOmdoc cons
	where
	  odmetadata = case mom of
	  	(Just m) -> toXmlTrees m;
		Nothing  -> [];
	  odcatalogue = case moc of
	  	(Just c) -> toXmlTrees c;
		Nothing  -> [];
	  omdoctree = xtag
		"omdoc"
		(fromAttrl oattr)
		(concat (odmetadata:odcatalogue:(map toXmlTrees items)))
	  cons =  [((\(NTree r _) -> (NTree r omdoctree) ) emptyRoot)]


{-
   Saves an Omdoc-Structure to a File
-}
writeOmdocToURI::String->Omdoc->IO ()
writeOmdocToURI f o = do
	run' $ writeDocument [(a_output_file, f), (a_issue_errors, v_0)] $
		writeableOmdoc o
	return ()

{-
   Just a quick check on a root-node if an error occured while parsing.
-}
validXml::XmlTrees->Bool
validXml t = case applyXmlFilter (getValue "status" .> isOfText (=="0")) t of
	[] -> False;
	 _ -> True;

-- a shortcut to showXmlTrees
showXmlTreesNS::XmlTrees->String
showXmlTreesNS = flip showXmlTrees ""

-- this function is used to apply XmlFilters an XmlTrees
applyXmlFilter::XmlFilter->XmlTrees->XmlTrees
applyXmlFilter f t = (id .> f) t

{-
   X M L F I L T E R S
   These filters have been created with the OMDoc-DTD in mind to filter out valid elements.
-}

xmlGetOmdoc::XmlFilter
xmlGetMetadata::XmlFilter
xmlGetCatalogue::XmlFilter
xmlGetOmdocItems::XmlFilter

xmlGetOmdoc = getChildren .> isomdoc
xmlGetMetadata = getChildren .> ismetadata
xmlGetCatalogue = getChildren .> iscatalogue
xmlWithoutTextNAttributes = getChildren `notContaining` (isXText +++ isXAttr)
-- this filter skips metadata and catalogue tags and text (\n)
-- Attributes are not excluded
--xmlGetOmdocItems = getChildren `notContaining` (ismetadata +++ iscatalogue +++ isXText)
-- This filter gets elements as specified by the OmDOC-DTD (1.1) 
xmlGetOmdocItems = getChildren .> ( isomtext
				+++ istype
				+++ isassertion
				+++ isalternative
				+++ isexample
				+++ isproof
				+++ isproofobject
				+++ isexercise
				+++ issolution
				+++ isomlet
				+++ isprivate
				+++ iscode
				+++ ispresentation
				+++ isomstyle
				+++ istheory
				+++ isomgroup
				+++ isignore
				+++ isref
				+++ istheory_inclusion
				+++ isdecomposition
				+++ isaxiom_inclusion
				)
				
xmlGetDCItems = getChildren .> (      isContributor
					+++ isCreator
					+++ isTitle
					+++ isSubject
					+++ isDescription
					+++ isPublisher
					+++ isType
					+++ isFormat
					+++ isSource
					+++ isLanguage
					+++ isRelation
					+++ isRights
					+++ isDate
					+++ isIdentifier
					)
xmlGetFMPItems = getChildren .> (   isassumption
				+++ isconclusion
				+++ isOMOBJ
				)
xmlGetCMPItems = getChildren .> (   isXText --- PCDATA
				+++ isOMOBJ
				+++ isomlet
				+++ iswith
				+++ isref
				+++ isignore
				)
				
xmlGetOMOBJItems = getChildren .> ( isOMS
				+++ isOMV
				+++ isOMI
				+++ isOMB
				+++ isOMSTR
				+++ isOMF
				+++ isOMA
				+++ isOMBIND
				+++ isOME
				+++ isOMATTR
				)
				
{-
   F U R T H E R  D A T A T Y P E S
   These datatypes are representations of the above filters.
   They all provide XmlItem-instances and - if appropriate - instances that mark them as containing other items.
-}
				
data InTheoryMathItem =
	  ITMIType XmlTrees
	| ITMIAssertion XmlTrees
	| ITMIAlternative XmlTrees
	| ITMIExample XmlTrees
	| ITMIProof XmlTrees
	| ITMIProofObject XmlTrees
	deriving Show
	
instance XmlItem InTheoryMathItem where
	fromXmlTrees (t:_)
		| (istype t) /= [] = ITMIType [t]
		| (isassertion t) /= [] = ITMIAssertion [t]
		| (isalternative t) /= [] = ITMIAlternative [t]
		| (isexample t) /= [] = ITMIExample [t]
		| (isproof t) /= [] = ITMIProof [t]
		| (isproofobject t) /= [] = ITMIProofObject [t]
	toXmlTrees (ITMIType t) = t
	toXmlTrees (ITMIAssertion t) = t
	toXmlTrees (ITMIAlternative t) = t
	toXmlTrees (ITMIExample t) = t
	toXmlTrees (ITMIProof t) = t
	toXmlTrees (ITMIProofObject t) = t
				
xmlInTheoryMathItem = (     istype
			+++ isassertion
			+++ isalternative
			+++ isexample
			+++ isproof
			+++ isproofobject
			)
			
data OtherMathItem =
	  OMITheoryInclusion XmlTrees
	| OMIDecomposition XmlTrees
	| OMIAxiomInclusion XmlTrees
	deriving Show
	
instance XmlItem OtherMathItem where
	fromXmlTrees (t:_) 
		| (istheory_inclusion t) /= [] = OMITheoryInclusion [t]
		| (isdecomposition t) /= [] = OMIDecomposition [t]
		| (isaxiom_inclusion t) /= [] = OMIAxiomInclusion [t]
	toXmlTrees (OMITheoryInclusion t) = t
	toXmlTrees (OMIDecomposition t) = t
	toXmlTrees (OMIAxiomInclusion t) = t
		
xmlOtherMathItem = (istheory_inclusion
		+++ isdecomposition
		+++ isaxiom_inclusion
		)
		
data AuxItem =
	  AIExercise XmlTrees
	| AISolution XmlTrees
	| AIOmlet XmlTrees
	| AIPrivate XmlTrees
	| AICode XmlTrees
	| AIPresentation XmlTrees
	| AIOmStyle XmlTrees
	deriving Show
	
instance XmlItem AuxItem where
	fromXmlTrees (t:_)
		| (isexercise t) /= [] = AIExercise [t]
		| (issolution t) /= [] = AISolution [t]
		| (isomlet t) /= [] = AIOmlet [t]
		| (isprivate t) /= [] = AIPrivate [t]
		| (iscode t) /= [] = AICode [t]
		| (ispresentation t) /= [] = AIPresentation [t]
		| (isomstyle t) /= [] = AIOmStyle [t]
	toXmlTrees (AIExercise t) = t
	toXmlTrees (AISolution t) = t
	toXmlTrees (AIOmlet t) = t
	toXmlTrees (AIPrivate t) = t
	toXmlTrees (AICode t) = t
	toXmlTrees (AIPresentation t) = t
	toXmlTrees (AIOmStyle t) = t
		
xmlAuxItem = (      isexercise
		+++ issolution
		+++ isomlet
		+++ isprivate
		+++ iscode
		+++ ispresentation
		+++ isomstyle
		)
		
data OnlyInTheoryItem =
	  OITISymbol XmlTrees
	| OITIAxiom XmlTrees
	| OITIDefinition XmlTrees
	| OITIAdt XmlTrees
	| OITIImports XmlTrees
	| OITIInclusion XmlTrees
	deriving Show
	
instance XmlItem OnlyInTheoryItem where
	fromXmlTrees (t:_)
		| (issymbol t) /= [] = OITISymbol [t]
		| (isaxiom t) /= [] = OITIAxiom [t]
		| (isdefinition t) /= [] = OITIDefinition [t]
		| (isadt t) /= [] = OITIAdt [t]
		| (isimports t) /= [] = OITIImports [t]
		| (isinclusion t) /= [] = OITIInclusion [t]
	toXmlTrees (OITISymbol t) = t
	toXmlTrees (OITIAxiom t) = t
	toXmlTrees (OITIDefinition t) = t
	toXmlTrees (OITIAdt t) = t
	toXmlTrees (OITIImports t) = t
	toXmlTrees (OITIInclusion t) = t
		
xmlOnlyInTheoryItem = (     issymbol
			+++ isaxiom
			+++ isdefinition
			+++ isadt
			+++ isimports
			+++ isinclusion
			)
			
-- data OtherOmdocItem

-- instance XmlItem OtherOmdocItem
			
xmlOtherOmdocItem = ( none )

data InTheoryOmdocItem =
	  ITOIOmText XmlTrees
	| ITOIInTheoryMathItem InTheoryMathItem
	| ITOIAuxItem AuxItem
	| ITOITheory XmlTrees
	| ITOIOmGroup XmlTrees
	| ITOIIgnore XmlTrees
	| ITOIRef XmlTrees
--	| ITOIOtherOmdocItem OtherOmdocItem

instance Show InTheoryOmdocItem where
	show (ITOIOmText t) = 
		"OmText (" ++ (getValueString "id" t) ++ "):\n" ++
			(xmlGetTextContent t) ++ "\n"
	show (ITOITheory t) = 
		"Theory: (" ++ (getValueString "id" t) ++ "):\n" ++
			(xmlGetTextContent t) ++ "\n"
	show (ITOIOmGroup t) =
		"OmGroup (" ++ (getValueString "id" t) ++ "):\n" ++
			(xmlGetTextContent t) ++ "\n"
	show (ITOIIgnore t) = 
		"Ignore (" ++ (getValueString "id" t) ++ "):\n" ++
			(xmlGetTextContent t) ++ "\n"
	show (ITOIRef t) = 
		"Ref (" ++ (getValueString "id" t) ++ "):\n" ++
			(xmlGetTextContent t) ++ "\n"
	show (ITOIInTheoryMathItem i) =
		"In-Theory-Math-Item:\n" ++ (show i) ++ "\n"
	show (ITOIAuxItem i) = 
		"Aux-Item:\n" ++ (show i) ++ "\n"


instance XmlItem InTheoryOmdocItem where
	fromXmlTrees (t:_)
		| (isomtext t) /= [] = ITOIOmText [t]
		| (istheory t) /= [] = ITOITheory [t]
		| (isomgroup t) /= [] = ITOIOmGroup [t]
		| (isignore t) /= [] = ITOIIgnore [t]
		| (isref t) /= [] = ITOIRef [t]
		| (xmlInTheoryMathItem t) /= [] = ITOIInTheoryMathItem (fromXmlTrees [t]) 
		| (xmlAuxItem t) /= [] = ITOIAuxItem (fromXmlTrees [t])
	toXmlTrees (ITOIOmText t) = t
	toXmlTrees (ITOITheory t) = t
	toXmlTrees (ITOIOmGroup t) = t
	toXmlTrees (ITOIIgnore t) = t
	toXmlTrees (ITOIRef t) = t
	toXmlTrees (ITOIInTheoryMathItem i) = toXmlTrees i
	toXmlTrees (ITOIAuxItem i) = toXmlTrees i
	

xmlInTheoryOmdocItem = (    isomtext
			+++ xmlInTheoryMathItem
			+++ xmlAuxItem
			+++ istheory
			+++ isomgroup
			+++ isignore
			+++ isref
			+++ xmlOtherOmdocItem
			)
		
-- OMDoc Items without Metadata and Catalogue
data OmdocItem =
	  OIInTheoryOmdocItem InTheoryOmdocItem
	| OIOtherMathItem OtherMathItem
	deriving Show
	
instance XmlItem OmdocItem where
	fromXmlTrees (t:_)
		| (xmlInTheoryOmdocItem t) /= [] = OIInTheoryOmdocItem (fromXmlTrees [t])
		| (xmlOtherMathItem t) /= [] = OIOtherMathItem (fromXmlTrees [t])
	toXmlTrees (OIInTheoryOmdocItem i) = toXmlTrees i
	toXmlTrees (OIOtherMathItem i) = toXmlTrees i
			
xmlOmdocItem = xmlInTheoryOmdocItem +++ xmlOtherMathItem

-- Used in Theorys
data InTheoryItem =
	  ITIOnlyInTheoryItem OnlyInTheoryItem
	| ITIInTheoryOmdocItem InTheoryOmdocItem

instance Show InTheoryItem where
	show (ITIOnlyInTheoryItem i) =
		"Only-In-Theory-Item : \n" ++ (show i) 
	show (ITIInTheoryOmdocItem i) =
		"In-Theory-Omdoc-Item : \n" ++ (show i) 
	
instance XmlItem InTheoryItem where
	fromXmlTrees (t:_)
		| (xmlOnlyInTheoryItem t) /= [] = ITIOnlyInTheoryItem (fromXmlTrees [t])
		| (xmlInTheoryOmdocItem t) /= [] = ITIInTheoryOmdocItem (fromXmlTrees [t])
	toXmlTrees (ITIOnlyInTheoryItem i) = toXmlTrees i
	toXmlTrees (ITIInTheoryOmdocItem i) = toXmlTrees i

xmlInTheoryItem = xmlOnlyInTheoryItem +++ xmlInTheoryOmdocItem

				

