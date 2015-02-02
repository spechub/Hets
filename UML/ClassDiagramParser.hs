module ClassDiagramParser where

import qualified Data.Map as Map
import System.IO
import Text.XML.Light
import UML
import Utils
import XMINames
import Data.Maybe



processPackage :: Element -> Package
processPackage el = Package {
        packageName = fromMaybe "" (findAttr nameName el),
        classes = cl,
        associations = Map.fromList (parse "uml:Association" (processAssociation cl) (findChildren packagedElementName el)),
        interfaces = Map.fromList (parse "uml:Interface" processInterface (findChildren packagedElementName el)),
        packageMerges = map (fromMaybe "" . findAttr (sName "mergedPackage")) (findChildren (sName "packageMerge") el),
        signals = Map.fromList (parse "uml:Signal" processSignal (findChildren packagedElementName el)),
        assoClasses = Map.fromList (parse "uml:AssociationClass" (processAssociationClass cl) (findChildren packagedElementName el))}
		where cl = Map.fromList (parse "uml:Class" processClass (findChildren packagedElementName el))


processAssociation :: Map.Map Id Class -> Element  -> (Id,Association)
processAssociation cmap el = (fromMaybe "" (findAttr attrIdName el), Association {ends = map (processEnds cmap) (findChildren (sName "ownedEnd") el)})

processEnds :: Map.Map Id Class -> Element -> End
processEnds emap el = End {endTarget = fromJust (Map.lookup (fromJust (findAttr (sName "type") el))  emap), label = processLabel el}


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

processAssociationClass :: Map.Map Id Class -> Element -> (Id, AssociationClass)
processAssociationClass emap el = (fromMaybe "" (findAttr attrIdName el)
                , AssociationClass {acClass = snd (processClass el), acAsso = snd (processAssociation emap el)})

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
