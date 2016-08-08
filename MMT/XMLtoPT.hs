{- |
Module      :  ./MMT/XMLtoPT.hs
Description :  parsing functions from XML to parse tree
Copyright   :
License     :
Maintainer  :  a.jakubauskas@jacobs-university.de
Stability   :  experimental
Portability :

Parsing functions from XML to parse tree
-}
module MMT.XMLtoPT where

import MMT.Tools
-- import qualified MMT.TestData as Test1 -- local file

import Control.Monad
import Data.Maybe
import Text.XML.Light
import Common.Id
import Common.Result

import Debug.Trace

readPT :: String -> IO [Content]
readPT fname = liftM parseXML (readFile fname)

parse :: String -> IO [Result Decl]
parse fname = do
    putStr $ "reading file " ++ fname ++ "\n"
    tree <- readPT fname
-- putStr $ "reading XML tree: \n" ++ (show (onlyElems tree)) ++ "\n\n"
    return (map parseDeclR (onlyElems tree))

-- get attribute value by key (string)
getAttByName :: String -> Element -> String
getAttByName x e = -- trace ("looking at:\n" ++ show x ++ "\nin\n" ++ show e) $
                   fromJust
        (findAttr QName {qName = x, qURI = Nothing, qPrefix = Nothing} e)

getAttByNameMaybe :: String -> Element -> Maybe String
getAttByNameMaybe x =
        findAttr QName {qName = x, qURI = Nothing, qPrefix = Nothing}

getAttByNameR :: String -> Element -> Result String
getAttByNameR x e = let
        maybeVal = findAttr QName
            {qName = x, qURI = Nothing, qPrefix = Nothing}
            e
        in
        case maybeVal of
            Just str -> Result [] (Just str)
            Nothing -> Result [] Nothing

{- TODO: a shorthand func that deals specifically with application case
   getSymbName :: Element -> (String,Maybe(String,String))
-}

{-
getElName :: Element -> String
getElName e = (qName.elName) e

makeQName :: String -> QName
makeQName n = QName {qName = n, qURI=Nothing, qPrefix=Nothing}
-}
parseDeclR :: Element -> Result Decl
parseDeclR e = let
                chil = elChildren e
                chilR = mapM parseTreeR chil
                in
                case maybeResult chilR of
                    (Just r) -> Result
                        (diags chilR)
                        (Just (Decl
                            (getAttByName "pattern" e)
                            (getAttByName "name" e) r))
                    Nothing -> Result (diags chilR) Nothing

parseTreeR :: Element -> Result Tree
parseTreeR e = let
        tree = parseNTreeR ((qName . elName) e ) e
        in
        tree

parseNTreeR :: String -> Element -> Result Tree
parseNTreeR "var" e = Result [] (Just (Variable (getAttByName "name" e)))
parseNTreeR "app" e = let
                    args = elChildren e
                    body = mapM parseTreeR args
                    pname = getAttByNameMaybe "pattern" e
                    iname = getAttByNameMaybe "instance" e
                    ref = case (pname, iname) of
                                (Just pn, Just inn) -> Just (pn, inn)
                                _ -> Nothing
                    in
                    case maybeResult body of
                    (Just r) ->
                        Result [] (Just
                            (Application
                                (getAttByName "name" e)
                                 ref
                                 r ))
                    Nothing -> Result (diags body) Nothing

parseNTreeR "bind" e = let
                     binder = getAttByName "binder" e
                     var = getAttByName "var" e
                     body = parseTreeR (head (elChildren e))
                     in
                     case maybeResult body of
                        (Just r) -> Result [] (Just (Bind binder var r))
                        Nothing -> Result [] Nothing
parseNTreeR "tbind" e = let
                      binder = getAttByName "binder" e
                      var = getAttByName "var" e
                      tp = parseTreeR (head (elChildren e))
                      body = parseTreeR (last (elChildren e))
                      in
                      case (maybeResult tp, maybeResult body) of
                        (Just t, Just b) -> Result [] (Just
                                            (Tbind binder var
                                            t b))
                        (_, _) -> Result
                            (diags tp ++ diags body)
                            Nothing
parseNTreeR str _ = let
                   msg = "error while parsing file " ++
                      -- file ++
                        ": unknown node <" ++ str ++ ">"
                   diag = Diag Error msg nullRange
                   in
                    Result [diag] Nothing
