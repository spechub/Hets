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
import UML2CL
import CommonLogic.AS_CommonLogic

main :: IO ()
main = do
	handle <- openFile "data/simplelibrary.xmi" ReadMode
        --handle <- openFile "data/uml.xmi" ReadMode
	--handle <- openFile "data/statemachine.xmi" ReadMode
        contents <- hGetContents handle
        putStr $ show (printText (translate (case parseXMLDoc contents of
                Nothing -> error contents
                Just el -> (parseModel el))))

parseModel :: Element -> Model
parseModel el = case findAttr typeName (head (findChildren packagedElementName el))  of 
		Just "uml:StateMachine" -> (parseStateMachine (head (findChildren packagedElementName el)))
		_ -> parseClassModel el
