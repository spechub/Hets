module UML.Parser where

import           System.IO

import           UML.ClassDiagramParser
import           UML.StateMachineParser
import           UML.UML
import           UML.XMINames

import           Data.Maybe

import           Common.GlobalAnnotations      (PrefixMap)

import           Text.ParserCombinators.Parsec
import           Text.XML.Light



basicSpecCM :: PrefixMap ->  GenParser Char st CM
basicSpecCM _ = do
                s <- many anyChar
                return $ parseUMLCDfromString s

parseUMLCDfromString :: String -> CM
parseUMLCDfromString s = case parseXMLDoc s of
                    Nothing -> error "Not a proper xmi-file"
                    Just el -> case parseModel el  of
                                ClassModel cma -> cma
                                _ -> error "unimplemented"

parseUMLCDfromFile :: FilePath -> IO CM
parseUMLCDfromFile fp =
  do
    handle <- openFile fp ReadMode
    contents <- hGetContents handle
    return $ parseUMLCDfromString contents

parseModel :: Element -> Model
parseModel el0 =     case findAttr (typeName xmiv) (head (findChildren packagedElementName el))  of
                        Just "uml:StateMachine" -> (parseStateMachine xmiv (head (findChildren packagedElementName el)))
                        _ -> parseClassModel (xmiv, umlv) el
                    where
                        el = fromJust $ findModelElement el0
                        xmiv = (qURI . attrKey) $ head $ filter (not . (Nothing ==) . qURI . attrKey) $ elAttribs el
                        umlv = qURI $ elName el --case filter ((Just "exporterVersion" ==).(findAttr nameName)) $ foldl (++) [] $ map (findChildren (sName "contents")) $ findChildren (sName "eAnnotations") el of
                                    --[] -> "5.0.0"
                                    --(dV:_) -> fromJust $ findAttr (sName "value") dV

findModelElement :: Element -> Maybe Element
findModelElement el0 = case (qName $ elName el0) == "Model" && (qPrefix $ elName el0) == Just "uml" of
                    True -> Just el0
                    False -> case filter (not . isNothing) $ map findModelElement (elChildren el0) of
                                [] -> Nothing
                                (x : _) -> x

isElem :: Maybe String -> String -> Element -> Bool
isElem xmiv s el = (findAttr (typeName xmiv) el) == Just s



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
