{- |
Description :  XMI parser for UML Class Diagrams
Copyright   :  (c) Martin Glauer

Maintainer  :  martin.glauer@st.ovgu.de
Stability   :  experimental

-}
module ClassDiagramParser where

import qualified Data.Map as Map
import System.IO
import Text.XML.Light
import UML
import Utils
import XMINames
import Data.Maybe


parseClassModel :: Element -> Model
parseClassModel el = ClassModel CM{
					cmName = fromJust (findAttr nameName el),
					cmClasses = classes pack,
					cmAssociations = associations pack,
					cmInterfaces = interfaces pack,
					cmPackageMerges = packageMerges pack,
					cmSignals = signals pack,
					cmAssociationClasses = packageAssociationClasses pack,
					cmPackages = packagePackages pack
				}
				where 	pack = processPackage cacmap semap el
					cacmap = Map.union cmap acmap
					cmap = Map.fromList $ (map (\(id,x) -> (id,CL x)) (collectRec "uml:Class" processClass el)) 
					acmap = Map.fromList $ (map (\(id,x) -> (id,AC x)) (collectRec "uml:AssociationClass" (processAssociationClass cmap semap) el))
					semapraw = collectSpecialEnds cacmap el 
					semap = (Map.fromList [(id, [x | (id2,x) <- semapraw, id == id2]) | id <- (Map.keys (Map.fromList semapraw))])
processPackage :: Map.Map Id ClassEntity -> Map.Map Id [End] -> Element -> Package
processPackage cmap semap el = Package {
			packageName = fromMaybe "" (findAttr nameName el),
			classes = Map.fromList $ map (\(id,CL x) -> (id,x)) (map ((\x -> (x,fromJust(Map.lookup x cmap))).(fromJust.(findAttr attrIdName))) (getChildrenType "uml:Class" el)),
			associations = Map.fromList (parse "uml:Association" (processAssociation cmap semap) lis),
			interfaces = Map.fromList (parse "uml:Interface" processInterface lis),
			packageMerges = map (fromMaybe "" . findAttr (sName "mergedPackage")) (findChildren (sName "packageMerge") el),
			packageAssociationClasses = Map.fromList $ map (\(id,AC x) -> (id,x)) (map ((\x -> (x,fromJust(Map.lookup x cmap))).(fromJust.(findAttr attrIdName))) (findChildren (sName "uml:AssociationClass") el)),
			signals = Map.fromList (parse "uml:Signal" processSignal lis),
			packagePackages = parse "uml:Package" (processPackage cmap semap) lis
		} 
		where lis = (findChildren packagedElementName el)

findPackageElements :: Element -> [Element]
findPackageElements el = filter (\x -> findAttr typeName x == Just "uml:Package") (findChildren packagedElementName el)


collectRec :: String -> (Element -> (Id,t)) -> Element -> [(Id,t)]
collectRec s f el =  (parse s f (findChildren packagedElementName el)) 
			++ (foldl (++) [] (map (collectRec s f) (findPackageElements el)))

collectSpecialEnds :: Map.Map Id ClassEntity -> Element -> [(Id,End)]
collectSpecialEnds cmap el =  (foldl (++) [] (map (classTranslator cmap) cl))  ++ (foldl (++) [] (map (collectSpecialEnds cmap) (findPackageElements el)))
				where 	cl = getChildrenType "uml:Class" el 

getChildrenType :: String -> Element -> [Element]
getChildrenType s el = filter (\x -> (findAttr typeName x) == Just s) (findChildren packagedElementName el)

classTranslator :: Map.Map Id ClassEntity -> Element -> [(Id,End)]
classTranslator cmap x = map (agrTranslator cmap) (filter (\x -> not ((findAttr (sName "aggregation") x) == Nothing)) (findChildren attributeName x))

agrTranslator :: Map.Map Id ClassEntity -> Element -> (Id,End)
agrTranslator cmap el = (fromJust (findAttr (sName "association") el),
			End{	endTarget= fromJust (Map.lookup (fromJust (findAttr (sName "type") el)) cmap), 
				label = processLabel el, 
				endType = case findAttr (sName "aggregation") el of
						Just "composite" -> Composition
						Just "aggregate" -> Aggregation
						Just t -> error $ "unknown aggregation type: " ++ t
				})
	

processAssociation :: Map.Map Id ClassEntity -> Map.Map Id [End] -> Element  -> (Id,Association)
processAssociation cmap semap el = (fromMaybe "" (findAttr attrIdName el), Association {ends = (map (processEnds cmap) (findChildren (sName "ownedEnd") el)) ++ fromMaybe [] (Map.lookup (fromJust(findAttr attrIdName el)) semap)})

processEnds :: Map.Map Id ClassEntity -> Element -> End
processEnds emap el = End {endTarget = (case (Map.lookup (fromJust (findAttr (sName "type") el))  emap) of 
							Just t -> t
							Nothing -> error $ "Key " ++ show (findAttr (sName "type") el) ++ " not found in " ++ (show emap)
					), label = processLabel el, endType = Normal}


processLabel :: Element -> Label
processLabel el = Label {upperValue = case findChildren (sName "upperValue") el of
                                [] -> "1"
                                lis -> fromMaybe "" (findAttr (sName "value") (head lis)),
                        lowerValue = case findChildren (sName "lowerValue") el of
                                [] -> "1"
                                lis -> fromMaybe "" (findAttr (sName "value") (head lis))}

processClass :: Element -> (Id, Class)
processClass el = (fromMaybe "" (findAttr attrIdName el)
                , Class { super = map processGeneralization (findChildren generalizationName el),
                        className = fromMaybe "" ( findAttr nameName el),
                        attr = map processAttribute (findChildren attributeName el),
                        proc = map processProcedure (findChildren procedureName el)})

processAssociationClass :: Map.Map Id ClassEntity -> Map.Map Id [End] -> Element -> (Id, AssociationClass)
processAssociationClass emap semap el = (fromMaybe "" (findAttr attrIdName el)
                , AssociationClass {acClass = snd (processClass el), acAsso = snd (processAssociation emap semap el)})

processSignal :: Element -> (Id, Signal)
processSignal el = (fromMaybe "" (findAttr attrIdName el),
                   Signal {sigSuper = map processGeneralization (findChildren generalizationName el),
                        signalName = (case findAttr nameName el of
                                        Nothing -> show el
                                        Just t -> t),
                        sigAttr = map processAttribute (findChildren attributeName el),
                        sigProc = map processProcedure (findChildren procedureName el)})

processProcedure :: Element -> Procedure
processProcedure el = Procedure {
                        procName = (case findAttr nameName el of
                                Nothing -> show el
                                Just t -> t),
                        procPara = (map processParameter (filter (not . isReturnParameter) (findChildren procParaName el))),
                        procReturnType = (case (filter (not . isReturnParameter) (findChildren procParaName el)) of
                                                                        [] -> Nothing
                                                                        lis -> Just (fromMaybe "" (findAttr attrTypeName1 (head lis)))),
                        procElemImports = map (fromMaybe "" . (findAttr (sName "importedElement"))) (findChildren (sName "elementImport") el),
                        procPackImports = map (fromMaybe "" . (findAttr (sName "importedPackage"))) (findChildren (sName "packageImport") el),
                        procVisibility = fromMaybe "" ((findAttr (sName "value")) (head (findChildren (sName "defaultValue") (head (filter (hasAttribute nameName "Visibility") (findChildren (sName "contents") (head (findChildren (sName "eAnnotations") el)) ))))))}

isReturnParameter :: Element -> Bool
isReturnParameter el = (findAttr procDirName el) == Just "return"

hasAttribute :: QName -> String -> Element -> Bool
hasAttribute n s el = case (findAttr n el) of
                        Nothing -> False
                        Just t -> (s == t)

processParameter :: Element -> (String, Type)
processParameter el = (case findAttr nameName el of
                        Nothing -> show el
                        Just t -> t
                        , case findAttr attrTypeName1 el of
                        Nothing -> show el
                        Just t -> t)

processAttribute :: Element -> Attribute
processAttribute el = Attribute {attrName = (case findAttr nameName el of
                        Nothing -> show el
                        Just t -> t),
                        attrType = (case findAttr attrTypeName1 el of
                                Nothing -> foldr (++) "" (map (fromMaybe "" . findAttr attrTypeName2) (findChildren attrTypeName1 el))
                                Just t -> t),
                        attrUpperValue = case (findChildren (sName "upperValue") el ) of
                                [] -> "1"
                                lis -> fromMaybe "" (findAttr (sName "value") (head lis)),
                        attrLowerValue = case (findChildren (sName "lowerValue") el) of
                                [] -> "1"
                                lis -> fromMaybe "" (findAttr (sName "value") (head lis)),
                        attrVisibility = fromMaybe "" ((findAttr (sName "value")) (head (findChildren (sName "defaultValue") (head (filter (hasAttribute nameName "Visibility") (findChildren (sName "contents") (head (findChildren (sName "eAnnotations") el)) ))))))}

{- processAttribute:: Attr -> Attribute
processAttribute at = Attribute{attrName = show at,
                        attrType = ""}--attrVal at} -}

processGeneralization :: Element -> Id
processGeneralization el = case findAttr attrGeneralName el of
                        Nothing -> show el
                        Just t -> t

processInterface :: Element -> (Id, Interface)
processInterface el = (fromMaybe "" (findAttr attrIdName el), Interface {interfaceName = (fromMaybe "" (findAttr nameName el))})

extractElementId :: Element -> Id
extractElementId el = case findAttr nameName el of
                        Nothing -> show el
                        Just t -> t


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
