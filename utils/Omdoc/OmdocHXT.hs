module OmdocHXT where

import Text.XML.HXT.Parser

import Omdoc_HXTAccess

{- TODO
   - element-processing-structures
-}

class XmlItem a where
	toXmlTrees::a->XmlTrees
	fromXmlTrees::XmlTrees->a
	getAttributeValue::String->a->String
	getAttributeValue _ _ = ""
	setAttributeValue::String->String->a->a
	setAttributeValue _ _ a = a

data Omdoc = Omdoc {
	omdoc		:: XmlTrees -- omdoc-element
	}
	
instance XmlItem Omdoc where
	toXmlTrees o = omdoc o
	fromXmlTrees t = Omdoc t
	getAttributeValue a o = getValueString a (omdoc o)
	setAttributeValue a v o = Omdoc (setValueString a v (omdoc o))
	
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
	
{- 
   Creates an Omdoc-Instance from XmlTrees
-}
mkOmdoc::XmlTrees->Omdoc
mkOmdoc t = Omdoc {
		omdoc = applyXmlFilter xmlGetOmdoc t
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
		
getOmdocItems::Omdoc->[OmdocItem]
getOmdocItems o =
	map (\t -> fromXmlTrees [t]) $ items o

-- M E T A D A T A

class (XmlItem a)=>HasMetadata a where
	getMetadata::a->XmlTrees
	getMetadata a = applyXmlFilter
		(getChildren .> ismetadata)
		$ toXmlTrees a
		
data OmdocMetadata = OmdocMetadata XmlTrees

instance HasMetadata OmdocMetadata where
	getMetadata (OmdocMetadata m) = m
		
instance XmlItem OmdocMetadata where
	fromXmlTrees t = OmdocMetadata t
	toXmlTrees (OmdocMetadata m) = m

-- Dublin Core Role

defRoleString = "aut"
defRoleLang = "en"

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
	
data DCRole = DCRole {
	 rlang	:: String -- ISO639, def 'en', xml:lang
	,rrole	:: String
	,rid	:: String
	,rstyle	:: String
	}
	
instance Show DCRole where
	show (DCRole l r i s) =
		("Role-ID : " ++ i ++ "\n"
		 ++ "Type : " ++ r ++ "\n"
		 ++ "Style : " ++ s ++ "\n"
		 ++ "Language : " ++ l ++ "\n"
		 )
		 
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

class IsAttributeList a where
	fromAttributeList::XmlTrees->a
	toAttributeList::a->[(String, String)]
	
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

class (XmlItem a)=>HasDCRole a where
	getDCRole::a->DCRole
	getDCRole a = fromAttributeList $ toXmlTrees a
	setDCRole::a->DCRole->a
	setDCRole a dcr =
		fromXmlTrees $
			setValueList (toAttributeList dcr) $
				toXmlTrees a
	
class (XmlItem a)=>HasTextContent a where
	getTextContent::a->String
	getTextContent a = xmlGetTextContent $ toXmlTrees a
	setTextContent::String->a->a
	setTextContent s a = fromXmlTrees $
		flip xmlSetTextContent s $ toXmlTrees a
		
-- Dublin Core Metadata
class (HasMetadata a)=>WithDublinCore a where
	getDCMItems::a->[DublinCoreMetadataItem]
	getDCMItems a = 
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter xmlGetDCItems $
			getMetadata a
	
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
	
instance XmlItem DublinCoreMetadataItem where
	fromXmlTrees (t:_) 
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
	
instance HasDCRole DublinCoreMetadataItem
			
instance HasTextContent DublinCoreMetadataItem
			
mkDCMCreator::(String, String, String, String)->String->DublinCoreMetadataItem
mkDCMCreator dcroles content =
	DCMCreator (
		xtag "Creator"
		  (fromAttrl (toAttributeList (mkDCRole dcroles)))
		  (xtext content)
		)

mkDCMContributor::(String, String, String, String)->String->DublinCoreMetadataItem
mkDCMContributor dcroles content =
	DCMContributor (
		xtag "Contributor"
		  (fromAttrl (toAttributeList (mkDCRole dcroles)))
		  (xtext content)
		)

mkOmdocMetadata::[DublinCoreMetadataItem]->OmdocMetadata
mkOmdocMetadata l = OmdocMetadata (
	xtag "metadata"
	[]
	(concatMap toXmlTrees l)
	)
	
instance HasMetadata Omdoc
instance WithDublinCore Omdoc
instance WithDublinCore OmdocMetadata

-- Items in CMP
	
data CMPItem =
	  PCDATA XmlTrees
	| OMOBJ XmlTrees
	| Omlet XmlTrees
	| With XmlTrees
	| Ref XmlTrees
	| Ignore XmlTrees
	deriving Show

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
	

class (XmlItem a)=>HasCMPItems a where
	getCMPItems::a->[CMPItem]
	getCMPItems a = map (\t -> fromXmlTrees [t]) $
		applyXmlFilter xmlGetCMPItems $
		toXmlTrees a
	
instance HasCMPItems DublinCoreMetadataItem

-- Items in MOBJ

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
	
class (XmlItem a)=>HasOMOBJItems a where
	getOMOBJItems::a->[OMOBJItem]
	getOMOBJItems a =
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter xmlGetOMOBJItems $
			toXmlTrees a
		
instance HasOMOBJItems DublinCoreMetadataItem

-- CMP

data CMP = CMP XmlTrees

instance XmlItem CMP where
	fromXmlTrees (t:_)
		| (isCMP t) /= [] = CMP [t]
	toXmlTrees (CMP t) = t
	
instance HasCMPItems CMP

class (XmlItem a)=>HasCMPs a where
	getCMPs::a->[CMP]
	getCMPs a = map (\t -> fromXmlTrees [t]) $
		applyXmlFilter (getChildren .> isCMP) $
			toXmlTrees a

-- Items in FMP

data FMPItem =
	  FMPAssumption XmlTrees
	| FMPConclusion XmlTrees
	| FMPOMOBJ XmlTrees
	
instance XmlItem FMPItem where
	fromXmlTrees (t:_)
		| (isassumption t) /= [] = FMPAssumption [t]
		| (isconclusion t) /= [] = FMPConclusion [t]
		| (isOMOBJ t) /= [] = FMPOMOBJ [t]
	toXmlTrees (FMPAssumption t) = t
	toXmlTrees (FMPConclusion t) = t
	toXmlTrees (FMPOMOBJ t) = t
	
class (XmlItem a)=>HasFMPItems a where
	getFMPItems::a->[FMPItem]
	getFMPItems a =
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter xmlGetFMPItems $
			toXmlTrees a
			
-- FMP

data FMP = FMP XmlTrees

instance XmlItem FMP where
	fromXmlTrees (t:_)
		| (isFMP t) /= [] = FMP [t]
	toXmlTrees (FMP t) = t
	
class (XmlItem a)=>HasFMPs a where
	getFMPs::a->[FMP]
	getFMPs a = 
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter isFMP $
			toXmlTrees a
	
instance HasFMPItems FMP

-- OmdocCatalogue

data OmdocCatalogue = OmdocCatalogue {
	odcatalogue :: XmlTrees
	}
	
instance Show OmdocCatalogue where
	show oc =
		show $ "Catalogue :\n" ++
			(concatMap (\n -> (show n)++"\n") $ getODCLocs oc)
	
instance XmlItem OmdocCatalogue where
	fromXmlTrees t = OmdocCatalogue t
	toXmlTrees o = odcatalogue o
	
data ODCLoc = ODCLoc {
	 ltheory :: String
	,lomdoc :: String
	,lcd :: String
	}
	
instance Show ODCLoc where
	show (ODCLoc t o c) =
		show $ "Theory: " ++ t ++ ", "
			++ "Omdoc: " ++ o ++ ", "
			++ "CD: " ++ c
	
mkODCLoc::(String, String, String)->ODCLoc
mkODCLoc (t, o, c) = ODCLoc t o c

instance XmlItem ODCLoc where
	fromXmlTrees t = ODCLoc {
		 ltheory = getValueString "theory" t
		,lomdoc = getValueString "omdoc" t
		,lcd = getValueString "cd" t
		}
	toXmlTrees l = xtag "loc"
		(fromAttrl [	 ("theory", (ltheory l))
				,("omdoc", (lomdoc l))
				,("cd", (lcd l))
			   ])
		[]

getODCLocs::OmdocCatalogue->[ODCLoc]
getODCLocs o = createLocs (applyXmlFilter (getChildren .> isloc) (odcatalogue o)) where
	createLocs [] = []
	createLocs (t:rest) = (fromXmlTrees [t]):(createLocs rest)
	
createODCatalogue::[ODCLoc]->OmdocCatalogue
createODCatalogue l = OmdocCatalogue (
	xtag "catalogue" (fromAttrl [])
		(concatMap toXmlTrees l)
		)
		
-- CommonName

data CommonName = CommonName XmlTrees

instance XmlItem CommonName where
	fromXmlTrees (t:_)
		| (iscommonname t) /= [] = CommonName [t]
	toXmlTrees (CommonName t) = t
	
instance HasCMPItems CommonName

instance Show CommonName where
	show (CommonName t) = show $
		(xmlGetTextContent t)
		++ " (" ++ (getValueString "xml:lang" t) ++ ")"
		
class (XmlItem a)=>HasCommonNames a where
	getCommonNames::a->[CommonName]
	getCommonNames a = map (\t -> fromXmlTrees [t]) $
		applyXmlFilter (getChildren .> iscommonname) $
		toXmlTrees a 
		
-- Theories

data Theory = Theory XmlTrees

instance Show Theory where
	show (th@(Theory t)) =
		show $
		"Theory :\nid: " ++ (getValueString "id" t)
		++ "\nCommonNames : (" ++ (show $ getCommonNames th) ++ ")\n" 

instance XmlItem Theory where
	fromXmlTrees (t:_)
		| (istheory t) /= [] = Theory [t]
	toXmlTrees (Theory t) = t
	
getTheories::Omdoc->[Theory]
getTheories o =
	foldr (\n ts -> (case n of
		(OIInTheoryOmdocItem (ITOITheory t)) -> ((Theory t):ts)
		_	-> ts
		) ) [] (getOmdocItems o)
		
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

xmlGetTextContent::XmlTrees->String
xmlGetTextContent t =
	concatMap (\(NTree (XText a) _) -> a) ((applyXmlFilter (getChildren .> isXText)) t)
	
xmlSetTextContent::XmlTrees->String->XmlTrees
xmlSetTextContent t@((NTree n l):r) s =
	((NTree n ((NTree (XText s) []):oc)):r)	where
	  oc = applyXmlFilter (getChildren `notContaining` isXText) t

getValueString::String->XmlTrees->String
getValueString a t = showXmlTreesNS $ getValue a (t!!0)

setValueString::String->String->XmlTrees->XmlTrees
setValueString a v t = applyXmlFilter (addAttr a v) t

setValueList::[(String, String)]->XmlTrees->XmlTrees
setValueList l t = foldr (\(a, v) t' -> setValueString a v t') t l

getID::Omdoc->String
getID (Omdoc { omdoc=od }) = getValueString "id" od

setID::Omdoc->String->Omdoc
setID o i = Omdoc {-(rootnode o)-} (setValueString "id" i (omdoc o))

getOmdocMetadata::Omdoc->OmdocMetadata
getOmdocMetadata o = OmdocMetadata $ metadata o

getOmdocCatalogue::Omdoc->OmdocCatalogue
getOmdocCatalogue o = OmdocCatalogue $ catalogue o

metadata::Omdoc->XmlTrees
metadata (Omdoc { omdoc=od }) = applyXmlFilter xmlGetMetadata od

catalogue::Omdoc->XmlTrees
catalogue (Omdoc { omdoc=od }) = applyXmlFilter xmlGetCatalogue od

items::Omdoc->XmlTrees
items (Omdoc { omdoc=od }) = applyXmlFilter xmlGetOmdocItems od
		
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
   Actually only the doctree component is written so it
   must always be consistent to the structure...
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

showXmlTreesNS::XmlTrees->String
showXmlTreesNS = flip showXmlTrees ""

applyXmlFilter::XmlFilter->XmlTrees->XmlTrees
applyXmlFilter f t = (id .> f) t

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

class (XmlItem a)=>HasInTheoryItems a where
	getInTheoryItems::a->[InTheoryItem]
	getInTheoryItems a =
		map (\t -> fromXmlTrees [t]) $
			applyXmlFilter (getChildren .> xmlInTheoryItem) $
				toXmlTrees a
				

