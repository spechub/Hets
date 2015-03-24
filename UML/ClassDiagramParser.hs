{- |
Description :  XMI parser for UML Class Diagrams
Copyright   :  (c) Martin Glauer

Maintainer  :  martin.glauer@st.ovgu.de
Stability   :  experimental

-}
module UML.ClassDiagramParser where

import qualified Data.Map as Map
import Text.XML.Light
import UML.UML
import UML.Utils
import UML.XMINames
import Data.Maybe
import Data.List

parseClassModel :: (Maybe String,Maybe String) -> Element -> Model
parseClassModel (xmiv,_) el = ClassModel CM{
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
                    pack = processPackage xmiv allmap semap el
                    allmap = Map.union emap $ Map.union cmap acmap
                    cmap = Map.fromList $ (map (\(id1,x) -> (id1,CL x)) (collectRec xmiv  "uml:Class" (processClass xmiv allmap) el)) 
                    emap = Map.fromList $ map (\(id1,x) -> (id1,EN x)) (collectRec xmiv  "uml:Enumeration" (processEnumeration xmiv) el)
                    acmap = Map.fromList $ (map (\(id1,x) -> (id1,AC x)) (collectRec xmiv  "uml:AssociationClass" (processAssociationClass xmiv (Map.union cmap emap) semap) el))
                    semapraw = collectSpecialEnds xmiv allmap el 
                    semap = (Map.fromList [(id1, [x | (id2,x) <- semapraw, id1 == id2]) | id1 <- (Map.keys (Map.fromList semapraw))])

processPackage :: Maybe String -> Map.Map Id ClassEntity -> Map.Map Id [End] -> Element -> Package
processPackage xmiv cmap semap el = Package {
            packageName = fromMaybe "" (findAttr nameName el),
            classes = Map.fromList $ map (\(id1,CL x) -> (id1,x)) (map ((\x -> (x,fromJust(Map.lookup x cmap))).(fromJust.(findAttr (attrIdName xmiv)))) (getChildrenType xmiv "uml:Class" el)),
            associations = Map.fromList (parse xmiv "uml:Association" (processAssociation xmiv  cmap semap) lis),
            interfaces = Map.fromList (parse xmiv "uml:Interface" (processInterface xmiv) lis),
            packageMerges = map (fromMaybe "" . findAttr (sName "mergedPackage")) (findChildren (sName "packageMerge") el),
            packageAssociationClasses = Map.fromList $ map (\(id1,AC x) -> (id1,x)) (map ((\x -> (x,fromJust(Map.lookup x cmap))).(fromJust.(findAttr (attrIdName xmiv)))) (findChildren (sName "uml:AssociationClass") el)),
            packageEnums = Map.fromList $ filterFromEntityMap xmiv cmap (\(EN x) -> x) (getChildrenType xmiv "uml:Enumeration" el),
            signals = Map.fromList (parse xmiv "uml:Signal" (processSignal xmiv cmap) lis),
            packagePackages = parse xmiv "uml:Package" (processPackage xmiv  cmap semap) lis
        } 
        where lis = (findChildren packagedElementName el)

filterFromEntityMap :: Maybe String -> (Map.Map Id ClassEntity) -> (ClassEntity -> t) -> [Element] -> [(Id, t)]
filterFromEntityMap xmiv emap f lis = map (\(id1,x) -> (id1,f x)) (map ((\x -> (x,fromJust(Map.lookup x emap))).(fromJust.(findAttr (attrIdName xmiv)))) lis)

findPackageElements :: Maybe String -> Element -> [Element]
findPackageElements xmiv el = filter (\x -> findAttr (typeName xmiv) x == Just "uml:Package") (findChildren packagedElementName el)


collectRec :: Maybe String -> String -> (Element -> (s,t)) -> Element -> [(s,t)]
collectRec xmiv s f el =  (parse xmiv s f (findChildren packagedElementName el)) 
            ++ (foldl (++) [] (map (collectRec xmiv s f) (findPackageElements xmiv el)))


collectSpecialEnds :: Maybe String -> Map.Map Id ClassEntity -> Element -> [(Id,End)]
collectSpecialEnds xmiv cmap el =  (foldl (++) [] (map (classSETranslator cmap) cl))  ++ (foldl (++) [] (map (collectSpecialEnds xmiv cmap) (findPackageElements xmiv el)))
                where     cl = getChildrenType xmiv "uml:Class" el 

getChildrenType :: Maybe String -> String -> Element -> [Element]
getChildrenType xmiv s el = filter (\x -> (findAttr (typeName xmiv) x) == Just s) (findChildren packagedElementName el)

classSETranslator :: Map.Map Id ClassEntity -> Element -> [(Id,End)]
classSETranslator cmap x = map (agrTranslator cmap) (filter (\y -> not ((findAttr (sName "association") y) == Nothing)) (findChildren attributeName x))
--classSETranslator cmap x = map (agrTranslator cmap) (filter (\x -> not ((findAttr (sName "aggregation") x) == Nothing)) (findChildren attributeName x))

agrTranslator :: Map.Map Id ClassEntity -> Element -> (Id,End)
agrTranslator cmap el = (fromJust (findAttr (sName "association") el),
            End{    endTarget= fromJust (Map.lookup (fromJust (findAttr (sName "type") el)) cmap), 
                label = processLabel el, 
                endType = case findAttr (sName "aggregation") el of
                        Just "composite" -> Composition
                        Just "aggregate" -> Aggregation
                        Nothing -> Normal
                        Just t -> error $ "unknown aggregation type: " ++ t,
                endName = findAttr nameName el
                })
    

processAssociation :: Maybe String -> Map.Map Id ClassEntity -> Map.Map Id [End] -> Element  -> (Id,Association)
processAssociation xmiv cmap semap el = (fromJust (findAttr (attrIdName xmiv) el), Association {ends = (map (processEnds xmiv cmap) (findChildren (sName "ownedEnd") el)) ++ fromMaybe [] (Map.lookup (fromJust(findAttr (attrIdName xmiv) el)) semap), assoName = an})
    where an = case (findAttr nameName el) of 
            Nothing -> {-trace ("No name at association (id:" ++ (fromJust (findAttr attrIdName el)) ++ "). Name substituted by id") $-} fromJust (findAttr (attrIdName xmiv) el)
            Just n -> n

processEnds :: Maybe String -> Map.Map Id ClassEntity -> Element -> End
processEnds xmiv emap el = End {endTarget = (case (Map.lookup (fromJust (findAttr (sName "type") el))  emap) of 
                            Just t -> t
                            Nothing -> error $ "Key " ++ show (findAttr (sName "type") el) ++ " not found in " ++ (show emap)
                    ), label = processLabel el, endType = Normal,
                endName = Just $ fromMaybe (fromJust $ findAttr (attrIdName xmiv) el) $ (findAttr nameName el)}


processLabel :: Element -> Label
processLabel el = Label {upperValue = case findChildren (sName "upperValue") el of
                                [] -> lv
                                (x:_) -> fromMaybe "*" (findAttr (sName "value") x),
                        lowerValue = lv}
                    where 
                        lv = case findChildren (sName "lowerValue") el of
                                [] -> "1"
                                (x:_) -> fromMaybe "1" (findAttr (sName "value") x)

processClass :: Maybe String -> (Map.Map Id ClassEntity) -> Element -> (Id, Class)
processClass xmiv emap el = (fromMaybe "" (findAttr (attrIdName xmiv) el)
                , Class { super = map (processGeneralization emap) (findChildren generalizationName el),
                        className = fromMaybe "" ( findAttr nameName el),
                        attr = map (processAttribute emap) (findChildren attributeName el),
                        proc = map (processProcedure emap) (findChildren procedureName el)})

processAssociationClass :: Maybe String -> Map.Map Id ClassEntity -> Map.Map Id [End] -> Element -> (Id, AssociationClass)
processAssociationClass xmiv emap semap el = (fromMaybe "" (findAttr (attrIdName xmiv) el)
                , AssociationClass {acClass = snd (processClass xmiv emap el), acAsso = snd (processAssociation xmiv emap semap el)})

processEnumeration :: Maybe String -> Element -> (Id,UML.UML.Enum)
processEnumeration xmiv el = (fromJust  (findAttr (attrIdName xmiv) el),en)
                 where en = Enum{enumName = fromJust  (findAttr nameName el), enumLiterals = map snd $ map (processLiteral xmiv en) (findChildren (sName "ownedLiteral") el)}
        
processLiteral :: Maybe String -> UML.UML.Enum -> Element -> (Id,Literal)
processLiteral xmiv en el = (fromJust  (findAttr (attrIdName xmiv) el), Literal{ literalName =  fromJust  (findAttr nameName el), literalOwner=en})

processSignal :: Maybe String -> (Map.Map Id ClassEntity) -> Element -> (Id, Signal)
processSignal xmiv emap el = (fromMaybe "" (findAttr (attrIdName xmiv) el),
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
                                                                        (x:_) -> Just $ processType emap x ),
                        procElemImports = map (fromMaybe "" . (findAttr (sName "importedElement"))) (findChildren (sName "elementImport") el),
                        procPackImports = map (fromMaybe "" . (findAttr (sName "importedPackage"))) (findChildren (sName "packageImport") el),
                        procVisibility = case (findChildren (sName "eAnnotations") el) of
                                            (x:_) -> fromMaybe "" ((findAttr (sName "value")) (head (findChildren (sName "defaultValue") (head (filter (hasAttribute nameName "Visibility") (findChildren (sName "contents") x))))))
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
                                (x:_) -> fromMaybe "" (findAttr (sName "value") x),
                        attrLowerValue = case (findChildren (sName "lowerValue") el) of
                                [] -> "1"
                                (x:_) -> fromMaybe "1" (findAttr (sName "value") x),
                        attrVisibility = case (findChildren (sName "eAnnotations") el) of
                                            (x:_) -> fromMaybe "" ((findAttr (sName "value")) (head (findChildren (sName "defaultValue") (head (filter (hasAttribute nameName "Visibility") (findChildren (sName "contents") x))))))
                                            [] -> ""}

processType :: (Map.Map Id ClassEntity) -> Element ->  Type
processType cmap el =    Type{umltype = t, typeUnique = not $ (findAttr (sName "isUnique") el) == Just "false", typeOrdered= (findAttr (sName "isOrdered") el) == Just "true"}   -- Defaults:  Unique = True, Ordered = False
                where     
                    t = case stripPrefix "pathmap://UML_LIBRARIES/UMLPrimitiveTypes.library.uml#" typeString of 
                        Nothing -> case Map.lookup typeString cmap of
                                Nothing -> Other typeString
                                Just x -> CE x 
                        Just "String" -> UMLString
                        Just "Integer" -> UMLInteger
                        Just "Bool" -> UMLBool
                        Just "Boolean" -> UMLBool
                        Just "UnlimitedNatural" -> UMLUnlimitedNatural
                        Just "Real" -> UMLReal
                        Just t1 -> error $ "unknown type: " ++ t1
                    typeString = (case findAttr attrTypeName1 el of
                                        Nothing -> foldr (++) "" (map (fromMaybe "" . findAttr attrTypeName2) (findChildren attrTypeName1 el))
                                        Just t1 -> t1)
                    
{- processAttribute:: Attr -> Attribute
processAttribute at = Attribute{attrName = show at,
                        attrType = ""}--attrVal at} -}

processGeneralization ::  (Map.Map Id ClassEntity) -> Element -> ClassEntity
processGeneralization emap el = case findAttr attrGeneralName el of
                        Nothing -> error $ show el
                        Just t ->fromJust $ Map.lookup t emap

processInterface :: Maybe String -> Element -> (Id, Interface)
processInterface xmiv el = (fromMaybe "" (findAttr (attrIdName xmiv) el), Interface {interfaceName = (fromMaybe "" (findAttr nameName el))})

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
