-- module Basic_UML where
import System.IO
import Text.XML.Light
import XMINames

import ClassDiagramParser
import Data.List.Split
import qualified Data.Map as Map
import StateMachineParser
import UML
import Utils
import Data.Maybe
main :: IO ()
main = do
	handle <- openFile "data/simplelibrary.xmi" ReadMode
        --handle <- openFile "data/uml.xmi" ReadMode
	--handle <- openFile "data/statemachine.xmi" ReadMode
        contents <- hGetContents handle
        putStr (show (case parseXMLDoc contents of
                Nothing -> [Err contents]
                Just el -> (parseModels (findChildren packagedElementName el))))

parseModels :: [Element] -> [Model]
parseModels lis = case (filter (isElem "uml:Package") lis) of 
	[] -> (ClassModel [Package {
		packageName = "__DefaultPackage__",
		classes = cl,
		associations = Map.fromList (parse "uml:Association" (processAssociation cl) lis),
		interfaces = Map.fromList (parse "uml:Interface" processInterface lis),
		packageMerges = map (fromMaybe "" . findAttr (sName "mergedPackage")) (filter (isElem "packageMerge") lis),
		signals = Map.fromList (parse "uml:Signal" processSignal lis),
		assoClasses = Map.fromList (parse "uml:AssociationClass" (processAssociationClass cl) lis)}]):(parseModelsWOClass lis)
			where cl = Map.fromList (parse "uml:Class" processClass lis)
	_ -> (ClassModel (parse "uml:Package" processPackage lis)) : (parseModelsWOClass lis)
	

parseModelsWOClass :: [Element] -> [Model]
parseModelsWOClass [] = []
parseModelsWOClass (el : lis) = case findAttr nameName el of
                        Just "State Machine" -> (parseStateMachine el) : (parseModelsWOClass lis)
                        -- Just "uml:Package" ->  (processPackage el):(parseModels lis)
                        _ -> parseModelsWOClass lis

isElem :: String -> Element -> Bool 
isElem s el = (findAttr typeName el) == Just s 




{- parseClassModel :: Element -> Model
parseClassModel el = ClassModel [Package{classes=(Map.fromList (parseClasses (findChildren packagedElementName el))), associations=(parseAssociations (findChildren packagedElementName el)), interfaces=(Map.fromList(parseInterfaces (findChildren packagedElementName el)))}] -}


{- parseXMItoUML :: IO()
parseXMItoUML = do
        putStr "Start \n"
        handle <- openFile "uml.xmi" ReadMode
        contents <- hGetContents handle
        case parseXMLDoc contents of
                Nothing -> putStr "VACIO"
                Just el -> let cm = ClassModel{ classes = Map.fromList ( parseClasses (findChildren packagedElementName el)),
                                                assos = parseAssociations (findChildren packagedElementName el)} in putStr ((show (classes cm)) ++ "\n" ++ (show (assos cm))) -}

-- starte machine


{- parseXMIToStateMachine = do
        putStr "Start \n"
        handle <- openFile "statemachine.xmi" ReadMode
        contents <- hGetContents handle
        case parseXMLDoc contents of
                Nothing -> putStr "VACIO"
                Just el -> let sm = Region{states = parseStates (findChildren smSubvertexName el), transitions=[show el]} in putStr ((show (states sm)) ++ "\n" ++ (show (transitions sm))) -}
