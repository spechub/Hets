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
                Nothing -> error contents
                Just el -> (parseModel el)))

parseModel :: Element -> Model
parseModel el = case findAttr typeName (head (findChildren packagedElementName el))  of 
		Just "uml:StateMachine" -> (parseStateMachine (head (findChildren packagedElementName el)))
		_ -> parseClassModel el

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
