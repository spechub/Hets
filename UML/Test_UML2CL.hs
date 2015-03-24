import System.IO
import Text.XML.Light
import UML.XMINames

import UML.ClassDiagramParser
import Data.List.Split
import qualified Data.Map as Map
import UML.StateMachineParser
import UML.UML
import UML.Utils
import Data.Maybe
import UML.UML2CL
import CommonLogic.AS_CommonLogic

main :: IO ()
main = do
    handle <- openFile "UML/data/statemachine_Till.xml" ReadMode
        --handle <- openFile "data/uml.xmi" ReadMode
    --handle <- openFile "data/statemachine.xmi" ReadMode
        contents <- hGetContents handle
        putStr $ show (printText (translateModel2Text (case parseXMLDoc contents of
                Nothing -> error contents
                Just el -> (parseModel el))))

parseModel :: Element -> Model
parseModel el0 =     case findAttr typeName (head (findChildren packagedElementName el))  of 
                        Just "uml:StateMachine" -> (parseStateMachine (head (findChildren packagedElementName el)))
                        _ -> parseClassModel el
                    where el =  case (elName el0) == modelName of 
                                    True -> el0
                                    False -> fromJust $ findElement modelName el0
