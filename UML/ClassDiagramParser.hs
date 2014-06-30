module ClassDiagramParser where

import Text.XML.Light
import System.IO
import XMINames
import UML
import Utils
import qualified Data.Map as Map

processPackage :: Element -> Package
processPackage el = Package{
	packageName = unjust (findAttr nameName el), 
	classes=(Map.fromList (parse "uml:Class" processClass (findChildren packagedElementName el))), 
	associations=(parse "uml:Association" processAssociation (findChildren packagedElementName el)), 
	interfaces=(Map.fromList(parse "uml:Interface" processInterface (findChildren packagedElementName el))),
	packageMerges = map (unjust.(findAttr (sName "mergedPackage"))) (findChildren (sName "packageMerge") el),
	signals=(Map.fromList (parse "uml:Signal" processSignal (findChildren packagedElementName el))),
	assoClasses=(Map.fromList (parse "uml:AssociationClass" processAssociationClass (findChildren packagedElementName el)))}
				

processAssociation :: Element -> Association
processAssociation el = Association{assoId = "", ends = map processEnds (findChildren (sName "ownedEnd") el)}

processEnds :: Element -> End
processEnds el = End{endTarget = unjust (findAttr (sName "type") el), label = processLabel el}


processLabel:: Element -> Label
processLabel el = Label{upperValue = case (findChildren (sName "upperValue") el ) of 
				[] -> "1"
				lis -> unjust (findAttr (sName "value") (head lis)),
			lowerValue = case (findChildren (sName "lowerValue") el) of 
				[] -> "1"
				lis -> unjust (findAttr (sName "value") (head lis))}

processClass :: Element -> (Id,Class)
processClass el= (unjust (findAttr attrIdName el)
		,Class{	super= map processGeneralization (findChildren generalizationName el),
			className = unjust ( findAttr nameName el),
			attr=map processAttribute (findChildren attributeName el),
			proc=map processProcedure (findChildren procedureName el)})

processAssociationClass :: Element -> (Id,AssociationClass)
processAssociationClass el= (unjust (findAttr attrIdName el)
		,AssociationClass{acClass = snd (processClass el), acAsso = processAssociation el})

processSignal :: Element -> (Id,Signal)
processSignal el= (case (findAttr attrIdName el) of 
			Nothing -> ""
			Just t -> t
		,Signal{sigSuper= map processGeneralization (findChildren generalizationName el),
			signalName = (case findAttr nameName el of 
					Nothing -> show el 
					Just t -> t),
			sigAttr=map processAttribute (findChildren attributeName el),
			sigProc=map processProcedure (findChildren procedureName el)})

processProcedure:: Element -> Procedure
processProcedure el = Procedure{
			procName = (case findAttr nameName el of 
				Nothing -> show el 
				Just t -> t),
			procPara = (map processParameter (filter  (not.isReturnParameter) (findChildren procParaName el))),
			procReturnType = (case (filter  (not.isReturnParameter) (findChildren procParaName el)) of 
									[] -> Nothing
									lis -> Just (unjust(findAttr attrTypeName1 (head lis)))),
			procElemImports = map (unjust.(findAttr (sName "importedElement"))) (findChildren (sName "elementImport") el),
			procPackImports = map (unjust.(findAttr (sName "importedPackage"))) (findChildren (sName "packageImport") el),
			procVisibility = unjust ((findAttr (sName "value")) (head (findChildren (sName "defaultValue") (head (filter (hasAttribute nameName "Visibility") (findChildren (sName "contents") (head (findChildren (sName "eAnnotations") el)) ))))))}

isReturnParameter:: Element -> Bool
isReturnParameter el = (findAttr procDirName el) == Just "return"

hasAttribute :: QName -> String -> Element -> Bool
hasAttribute n s el = case (findAttr n el) of 
			Nothing -> False
			Just t -> (s == t)

processParameter::Element -> (String,Type)
processParameter el = (case findAttr nameName el of 
			Nothing -> show el 
			Just t -> t
			,case findAttr attrTypeName1 el of 
			Nothing -> show el 
			Just t -> t)

processAttribute:: Element -> Attribute
processAttribute el = Attribute{attrName = (case findAttr nameName el of 
			Nothing -> show el 
			Just t -> t),
			attrType = (case findAttr attrTypeName1 el of 
				Nothing -> foldr (++) "" (map (unjust.findAttr attrTypeName2) (findChildren attrTypeName1 el))
				Just t -> t),
			attrUpperValue = case (findChildren (sName "upperValue") el ) of 
				[] -> "1"
				lis -> unjust (findAttr (sName "value") (head lis)),
			attrLowerValue = case (findChildren (sName "lowerValue") el) of 
				[] -> "1"
				lis -> unjust (findAttr (sName "value") (head lis)),
			attrVisibility = unjust ((findAttr (sName "value")) (head (findChildren (sName "defaultValue") (head (filter (hasAttribute nameName "Visibility") (findChildren (sName "contents") (head (findChildren (sName "eAnnotations") el)) ))))))}

{-processAttribute:: Attr -> Attribute
processAttribute at = Attribute{attrName = show at,
			attrType = ""}--attrVal at}-}

processGeneralization :: Element -> Id
processGeneralization el = case findAttr attrGeneralName el of 
			Nothing -> show el 
			Just t -> t

processInterface :: Element -> (Id, Interface)
processInterface el = (unjust (findAttr attrIdName el), Interface{interfaceName=(unjust(findAttr nameName el))})

extractElementId :: Element -> Id
extractElementId el = case findAttr nameName el of 
			Nothing -> show el 
			Just t -> t


parse::String -> (Element -> a) -> [Element] -> [a]
parse _ _ [] = []
parse s f (el:lis) = 
	case (findAttr typeName el) of 
		Just t -> case s == t of 
			True -> ((f el):(parse s f lis))
			False -> parse s f lis
		_ -> parse s f lis

{-
parseAssociations :: [Element] -> [Association]
parseAssociations [] = []
parseAssociations (el:lis) = 
	case (findAttr typeName el) of
		Nothing -> parseAssociations lis
		Just "uml:Association" -> ((processAssociation el):(parseAssociations lis))
		Just _ -> parseAssociations lis

parseInterfaces :: [Element] -> [(Id,Interface)]
parseInterfaces [] = []
parseInterfaces (el:lis) = case (findAttr typeName el) of
		Just "uml:Interface" -> ((processInterface el):(parseInterfaces lis))
		_ -> parseInterfaces lis

parsePackages :: [Element] -> [Package]
parsePackages [] = []
parsePackages (el:lis) = case (findAttr typeName el) of
		Nothing -> parsePackages lis
		Just "uml:Package" -> ((processPackage el):(parsePackages lis))
		Just _ -> parsePackages lis
-}

