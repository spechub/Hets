--module Basic_UML where
import Text.XML.Light
import System.IO
import XMINames

import Data.List.Split
import UML
import ClassDiagramParser
import StateMachineParser
import qualified Data.Map as Map
import Utils

main :: IO()
main = do 
	handle <- openFile "uml.xmi" ReadMode 
	contents <- hGetContents handle 
	putStr (show  (case parseXMLDoc contents of
		Nothing -> [Err contents]
		Just el -> (parseModels (findChildren packagedElementName el))))

parseModels::[Element] -> [Model]
parseModels lis = (ClassModel (parsePackages lis)):(parseModelsWOClass lis)

parseModelsWOClass::[Element] -> [Model]
parseModelsWOClass [] = []
parseModelsWOClass (el:lis) = case findAttr nameName el of 
			Just "State Machine" ->  (parseStateMachine el):(parseModelsWOClass lis)
			--Just "uml:Package" ->  (processPackage el):(parseModels lis)	
			_ -> parseModelsWOClass lis



--parseClassModel :: Element -> Model
--parseClassModel el = ClassModel [Package{classes=(Map.fromList (parseClasses (findChildren packagedElementName el))), associations=(parseAssociations (findChildren packagedElementName el)), interfaces=(Map.fromList(parseInterfaces (findChildren packagedElementName el)))}]

	
{-parseXMItoUML :: IO()
parseXMItoUML = do
	putStr "Start \n"
	handle <- openFile "uml.xmi" ReadMode
	contents <- hGetContents handle
	case parseXMLDoc contents of
		Nothing -> putStr "VACIO"
		Just el -> let cm = ClassModel{ classes = Map.fromList ( parseClasses (findChildren packagedElementName el)), 
						assos = parseAssociations (findChildren packagedElementName el)} in putStr ((show (classes cm)) ++ "\n" ++ (show (assos cm)))-}

-- starte machine



{-parseXMIToStateMachine = do 
	putStr "Start \n"
	handle <- openFile "statemachine.xmi" ReadMode
	contents <- hGetContents handle
	case parseXMLDoc contents of
		Nothing -> putStr "VACIO"
		Just el -> let sm = Region{states = parseStates (findChildren smSubvertexName el), transitions=[show el]} in putStr ((show (states sm)) ++ "\n" ++ (show (transitions sm)))-}
