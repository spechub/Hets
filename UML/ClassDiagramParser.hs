{- |
Description :  XMI parser for UML Class Diagrams
Copyright   :  (c) Martin Glauer

Maintainer  :  martin.glauer@st.ovgu.de
Stability   :  experimental

-}
module UML.ClassDiagramParser where

import qualified Data.Map as Map
import System.IO
import Text.XML.Light
import UML.UML
import UML.Utils
import UML.XMINames
import Data.Maybe
import Data.List
import Debug.Trace

parseClassModel :: Element -> Model
parseClassModel el = ClassModel CM{
					cmName = fromJust (findAttr nameName el),
					cmClasses = classes pack,
					cmAssociations = associations pack,
					cmInterfaces = interfaces pack,
					cmPackageMerges = packageMerges pack,
					cmSignals = signals pack,
					cmAssociationClasses = packageAssociationClasses pack,
					cmPackages = packagePackages pack,
					cmEnums = packageEnums pack
				}
				where 	
					pack = processPackage allmap semap el
					allmap = Map.union emap $ Map.union cmap acmap
					cmap = Map.fromList $ (map (\(id,x) -> (id,CL x)) (collectRec "uml:Class" (processClass allmap) el)) 
					emap = Map.fromList $ map (\(id,x) -> (id,EN x)) (collectRec "uml:Enumeration" processEnumeration el)
					acmap = Map.fromList $ (map (\(id,x) -> (id,AC x)) (collectRec "uml:AssociationClass" (processAssociationClass (Map.union cmap emap) semap) el))
					semapraw = collectSpecialEnds allmap el 
					semap = (Map.fromList [(id, [x | (id2,x) <- semapraw, id == id2]) | id <- (Map.keys (Map.fromList semapraw))])

processPackage :: Map.Map Id ClassEntity -> Map.Map Id [End] -> Element -> Package
processPackage cmap semap el = Package {
			packageName = fromMaybe "" (findAttr nameName el),
			classes = Map.fromList $ map (\(id,CL x) -> (id,x)) (map ((\x -> (x,fromJust(Map.lookup x cmap))).(fromJust.(findAttr attrIdName))) (getChildrenType "uml:Class" el)),
			associations = Map.fromList (parse "uml:Association" (processAssociation cmap semap) lis),
			interfaces = Map.fromList (parse "uml:Interface" processInterface lis),
			packageMerges = map (fromMaybe "" . findAttr (sName "mergedPackage")) (findChildren (sName "packageMerge") el),
			packageAssociationClasses = Map.fromList $ map (\(id,AC x) -> (id,x)) (map ((\x -> (x,fromJust(Map.lookup x cmap))).(fromJust.(findAttr attrIdName))) (findChildren (sName "uml:AssociationClass") el)),
			packageEnums = Map.fromList $ filterFromEntityMap cmap (\(EN x) -> x) (getChildrenType "uml:Enumeration" el),
			signals = Map.fromList (parse "uml:Signal" (processSignal cmap) lis),
			packagePackages = parse "uml:Package" (processPackage cmap semap) lis
		} 
		where lis = (findChildren packagedElementName el)

filterFromEntityMap :: (Map.Map Id ClassEntity) -> (ClassEntity -> t) -> [Element] -> [(Id, t)]
filterFromEntityMap emap f lis = map (\(id,x) -> (id,f x)) (map ((\x -> (x,fromJust(Map.lookup x emap))).(fromJust.(findAttr attrIdName))) lis)

findPackageElements :: Element -> [Element]
findPackageElements el = filter (\x -> findAttr typeName x == Just "uml:Package") (findChildren packagedElementName el)


collectRec :: String -> (Element -> (s,t)) -> Element -> [(s,t)]
collectRec s f el =  (parse s f (findChildren packagedElementName el)) 
			++ (foldl (++) [] (map (collectRec s f) (findPackageElements el)))


collectSpecialEnds :: Map.Map Id ClassEntity -> Element -> [(Id,End)]
collectSpecialEnds cmap el =  (foldl (++) [] (map (classSETranslator cmap) cl))  ++ (foldl (++) [] (map (collectSpecialEnds cmap) (findPackageElements el)))
				where 	cl = getChildrenType "uml:Class" el 

getChildrenType :: String -> Element -> [Element]
getChildrenType s el = filter (\x -> (findAttr typeName x) == Just s) (findChildren packagedElementName el)

classSETranslator :: Map.Map Id ClassEntity -> Element -> [(Id,End)]
classSETranslator cmap x = map (agrTranslator cmap) (filter (\x -> not ((findAttr (sName "association") x) == Nothing)) (findChildren attributeName x))
--classSETranslator cmap x = map (agrTranslator cmap) (filter (\x -> not ((findAttr (sName "aggregation") x) == Nothing)) (findChildren attributeName x))

agrTranslator :: Map.Map Id ClassEntity -> Element -> (Id,End)
agrTranslator cmap el = (fromJust (findAttr (sName "association") el),
			End{	endTarget= fromJust (Map.lookup (fromJust (findAttr (sName "type") el)) cmap), 
				label = processLabel el, 
				endType = case findAttr (sName "aggregation") el of
						Just "composite" -> Composition
						Just "aggregate" -> Aggregation
						Nothing -> Normal
						Just t -> error $ "unknown aggregation type: " ++ t,
				endName = findAttr nameName el
				})
	

processAssociation :: Map.Map Id ClassEntity -> Map.Map Id [End] -> Element  -> (Id,Association)
processAssociation cmap semap el = (fromJust (findAttr attrIdName el), Association {ends = (map (processEnds cmap) (findChildren (sName "ownedEnd") el)) ++ fromMaybe [] (Map.lookup (fromJust(findAttr attrIdName el)) semap), assoName = an})
	where an = case (findAttr nameName el) of 
			Nothing -> {-trace ("No name at association (id:" ++ (fromJust (findAttr attrIdName el)) ++ "). Name substituted by id") $-} fromJust (findAttr attrIdName el)
			Just n -> n

processEnds :: Map.Map Id ClassEntity -> Element -> End
processEnds emap el = End {endTarget = (case (Map.lookup (fromJust (findAttr (sName "type") el))  emap) of 
							Just t -> t
							Nothing -> error $ "Key " ++ show (findAttr (sName "type") el) ++ " not found in " ++ (show emap)
					), label = processLabel el, endType = Normal,
				endName = findAttr nameName el}


processLabel :: Element -> Label
processLabel el = Label {upperValue = case findChildren (sName "upperValue") el of
                                [] -> "1"
                                (x:lis) -> fromMaybe "*" (findAttr (sName "value") x),
                        lowerValue = case findChildren (sName "lowerValue") el of
                                [] -> "1"
                                (x:lis) -> fromMaybe "1" (findAttr (sName "value") x)}

processClass :: (Map.Map Id ClassEntity) -> Element -> (Id, Class)
processClass emap el = (fromMaybe "" (findAttr attrIdName el)
                , Class { super = map (processGeneralization emap) (findChildren generalizationName el),
                        className = fromMaybe "" ( findAttr nameName el),
                        attr = map (processAttribute emap) (findChildren attributeName el),
                        proc = map (processProcedure emap) (findChildren procedureName el)})

processAssociationClass :: Map.Map Id ClassEntity -> Map.Map Id [End] -> Element -> (Id, AssociationClass)
processAssociationClass emap semap el = (fromMaybe "" (findAttr attrIdName el)
                , AssociationClass {acClass = snd (processClass emap el), acAsso = snd (processAssociation emap semap el)})

processEnumeration :: Element -> (Id,UML.UML.Enum)
processEnumeration el = (fromJust  (findAttr attrIdName el),en)
		 		where en = Enum{enumName = fromJust  (findAttr nameName el), enumLiterals = map snd $ map (processLiteral en) (findChildren (sName "ownedLiteral") el)}
		
processLiteral :: UML.UML.Enum -> Element -> (Id,Literal)
processLiteral en el = (fromJust  (findAttr attrIdName el), Literal{ literalName =  fromJust  (findAttr nameName el), literalOwner=en})

processSignal :: (Map.Map Id ClassEntity) -> Element -> (Id, Signal)
processSignal emap el = (fromMaybe "" (findAttr attrIdName el),
                   Signal {sigSuper = map (processGeneralization emap) (findChildren generalizationName el),
                        signalName = (case findAttr nameName el of
                                        Nothing -> show el
                                        Just t -> t),
                        sigAttr = map (processAttribute emap) (findChildren attributeName el),
                        sigProc = map (processProcedure emap) (findChildren procedureName el)})

processProcedure :: (Map.Map Id ClassEntity) -> Element -> Procedure
processProcedure emap el = Procedure {
                        procName = (case findAttr nameName el of
                                Nothing -> show el
                                Just t -> t),
                        procPara = (map (processAttribute emap) (filter (not . isReturnParameter) (findChildren procParaName el))),
                        procReturnType = (case (filter (isReturnParameter) (findChildren procParaName el)) of
                                                                        [] -> Nothing
                                                                        (x:lis) -> Just $ processType emap x ),
                        procElemImports = map (fromMaybe "" . (findAttr (sName "importedElement"))) (findChildren (sName "elementImport") el),
                        procPackImports = map (fromMaybe "" . (findAttr (sName "importedPackage"))) (findChildren (sName "packageImport") el),
                        procVisibility = case (findChildren (sName "eAnnotations") el) of
											(x:lis) -> fromMaybe "" ((findAttr (sName "value")) (head (findChildren (sName "defaultValue") (head (filter (hasAttribute nameName "Visibility") (findChildren (sName "contents") x))))))
											[] -> ""
}

isReturnParameter :: Element -> Bool
isReturnParameter el = (findAttr procDirName el) == Just "return"

hasAttribute :: QName -> String -> Element -> Bool
hasAttribute n s el = case (findAttr n el) of
                        Nothing -> False
                        Just t -> (s == t)

processParameter :: (Map.Map Id ClassEntity) -> Element -> (String, Type)
processParameter emap el = (case findAttr nameName el of
		                Nothing -> show el
		                Just t -> t,
			processType emap el )

processAttribute :: (Map.Map Id ClassEntity) -> Element -> Attribute
processAttribute emap el = Attribute {attrName = (case findAttr nameName el of
                        Nothing -> show el
                        Just t -> t),
                        attrType = processType emap el,
                        attrUpperValue = case (findChildren (sName "upperValue") el ) of
                                [] -> "1"
                                (x:lis) -> fromMaybe "" (findAttr (sName "value") x),
                        attrLowerValue = case (findChildren (sName "lowerValue") el) of
                                [] -> "1"
                                (x:lis) -> fromMaybe "" (findAttr (sName "value") x),
                        attrVisibility = case (findChildren (sName "eAnnotations") el) of
											(x:lis) -> fromMaybe "" ((findAttr (sName "value")) (head (findChildren (sName "defaultValue") (head (filter (hasAttribute nameName "Visibility") (findChildren (sName "contents") x))))))
											[] -> ""}

processType :: (Map.Map Id ClassEntity) -> Element ->  Type
processType cmap el =	Type{umltype = t, typeUnique = not $ (findAttr (sName "isUnique") el) == Just "false", typeOrdered= (findAttr (sName "isOrdered") el) == Just "true"}   -- Defaults:  Unique = True, Ordered = False
				where 	t = case stripPrefix "pathmap://UML_LIBRARIES/UMLPrimitiveTypes.library.uml#" typeString of 
						Nothing -> case Map.lookup typeString cmap of
								Nothing -> Other typeString
								Just x -> CE x 
						Just "String" -> UMLString
						Just "Integer" -> UMLInteger
						Just "Bool" -> UMLBool
						Just "Boolean" -> UMLBool
						Just "UnlimitedNatural" -> UMLUnlimitedNatural
						Just "Real" -> UMLReal
						Just t -> error $ "unknown type: " ++ t
					typeString = (case findAttr attrTypeName1 el of
                                		Nothing -> foldr (++) "" (map (fromMaybe "" . findAttr attrTypeName2) (findChildren attrTypeName1 el))
                                		Just t -> t)
					
{- processAttribute:: Attr -> Attribute
processAttribute at = Attribute{attrName = show at,
                        attrType = ""}--attrVal at} -}

processGeneralization ::  (Map.Map Id ClassEntity) -> Element -> ClassEntity
processGeneralization emap el = case findAttr attrGeneralName el of
                        Nothing -> error $ show el
                        Just t ->fromJust $ Map.lookup t emap

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
