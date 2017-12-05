module UML.Parser where

import           System.IO

import           UML.ClassDiagramParser
import           UML.StateMachineParser
import           UML.StateMachine
import           UML.UML
import           UML.XMINames

import           Data.Maybe
import           Data.List.Split
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
                                x -> error $ "Modeltype unimplemented: " ++ (show x)

parseUMLCDfromFile :: FilePath -> IO CM
parseUMLCDfromFile fp =
  do
    handle <- openFile fp ReadMode
    contents <- hGetContents handle
    return $ parseUMLCDfromString contents


basicSpecSM :: PrefixMap ->  GenParser Char st StateMachine
basicSpecSM _ = do
                s <- many anyChar
                return $ parseUMLSMfromString s

parseUMLSMfromString :: String -> StateMachine
parseUMLSMfromString s = case parseXMLDoc s of
                    Nothing -> error "Not a proper xmi-file"
                    Just el -> case parseModel el  of
                                SM sm -> sm
                                _ -> error "unimplemented"


parseModel :: Element -> Model
parseModel el0 = case findChildren packagedElementName el of 
                        (x:_) -> case Just smPrefix == (findAttr (typeName xmiv) x) of
                            True -> case findChildren packagedElementName el of 
                                (y:_) -> SM (parseStateMachine xmiv y)
                                [] -> error "No packagedElement found"
                            False -> parseClassModel prefix (xmiv, umlv) el
                   
                                        --[] -> "5.0.0"
                                        --(dV:_) -> fromJust $ findAttr (sName "value") dV
                        _ -> error $ "No PackagedElement found: " ++ (show $ elChildren el) 
                     where
                        el = fromMaybe (error "No ModelElement found") $ findModelElement el0
                        xmiv =  case filter (not . (Nothing ==) . qURI . attrKey) $ elAttribs el of  
                                    [] -> Nothing
                                    (x:_) ->  (qURI . attrKey) x
                        prefix = head (splitOn ":" $ fromMaybe "uml" $ findAttr (typeName xmiv) $ head $ findChildren packagedElementName el)
                        smPrefix = prefix ++ ":StateMachine"
                        umlv = qURI $ elName el --case filter ((Just "exporterVersion" ==).(findAttr nameName)) $ foldl (++) [] $ map (findChildren (sName "contents")) $ findChildren (sName "eAnnotations") el of
findModelElement :: Element -> Maybe Element
findModelElement el0 = case findChildren packagedElementName el0 of
                        [] -> case filter (not . isNothing) $ map findModelElement (elChildren el0) of
                                [] -> Nothing
                                [Just x] -> Just x
                                _ -> error "Multiple models in a single XMI are not supported"
                        _ -> Just el0

{-case ((qName $ elName el0) == "Model" && (qPrefix $ elName el0) == Just "uml") of -- || ((qName $ elName el0) == "XMI") of
                    True -> Just el0
                    False -> case filter (not . isNothing) $ map findModelElement (elChildren el0) of
                                [] -> Nothing
                                (x : _) -> x-}

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
