module ClassDiagramParser where

import Text.XML.Light
import System.IO
import XMINames
import UML
import Utils
import qualified Data.Map as Map

processPackage :: Element -> Package
processPackage el = Package{packageName = unjust (findAttr nameName el), 
classes=(Map.fromList (parseClasses (findChildren packagedElementName el))), 
associations=(parseAssociations (findChildren packagedElementName el)), 
interfaces=(Map.fromList(parseInterfaces (findChildren packagedElementName el))),
packageMerges = map (unjust.(findAttr (sName "mergedPackage"))) (findChildren (sName "packageMerge") el)}
				

processAssociation :: Element -> Association
processAssociation el = Association{ends = map processEnds (findChildren (sName "ownedEnd") el)}

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
processClass el= (case (findAttr attrIdName el) of 
			Nothing -> ""
			Just t -> t
		,Class{	super= map processGeneralization (findChildren generalizationName el),
			className = (case findAttr nameName el of 
					Nothing -> show el 
					Just t -> t),
			attr=map processAttribute (findChildren attributeName el),
			proc=map processProcedure (findChildren procedureName el)})

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
			procPackImports = map (unjust.(findAttr (sName "importedPackage"))) (findChildren (sName "packageImport") el)}

isReturnParameter:: Element -> Bool
isReturnParameter el =  (findAttr procDirName el) == Just "return"

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
			Just t -> t)}

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

parseClasses :: [Element] -> [(Id,Class)]
parseClasses [] = [] 
parseClasses (el:lis)  =
	case (findAttr typeName el) of 
		Nothing -> parseClasses lis
		Just "uml:Class" -> ((processClass el):(parseClasses lis))
		Just _ -> parseClasses lis


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

