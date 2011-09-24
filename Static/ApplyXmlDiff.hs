 {- |
Module      :  $Header$
Description :  xml input for Hets development graphs
Copyright   :  (c) Simon Ulbricht, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (DevGraph)

change an Xml-DGraph according to XmlDiff-data.
-}

module Static.ApplyXmlDiff where

import Static.XGraph
import Static.DgUtils

import Common.XUpdate
import Common.XSimplePath
import Common.Utils (readMaybe)

import Control.Monad

import qualified Data.Map as Map

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

data SimpleChanges = SimpleChanges { removeNodes :: [NodeName]
                                   , removeLinks :: [EdgeId]
                                   , renamings :: [(NodeName, NodeName)]
                                   , renumberings :: [(EdgeId, EdgeId)]
                                   , updateNodes :: Map.Map NodeName XNode
                                   , updateLinks :: Map.Map EdgeId XLink
                                   , addNodes :: [XNode]
                                   , addLinks :: [XLink]
                                   } deriving Show 

emptyChanges :: SimpleChanges
emptyChanges = SimpleChanges [] [] [] [] Map.empty Map.empty [] []

printXmlDiff :: Element -> String -> IO ()
printXmlDiff el diff = undefined

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = changeXml el diff
  
toElement :: Monad m => Cursor -> m Element
toElement cr = case current $ root cr of
    Elem e -> return e
    _ -> fail "cannot convert Cursor into Element"

{- determine change for an add operation.
NOTE: this will purposfully fail for any other cases than add entire Node/Link!
-}
mkAddCh_fullElem :: Monad m => SimpleChanges -> AddChange -> m SimpleChanges
mkAddCh_fullElem sChgs addCh = case addCh of
  -- insert entire Node
  AddElem e | nameString e == "DGNode" -> do
    n <- mkXNode e
    return sChgs { addNodes = n : addNodes sChgs }
  -- insert entire link
  AddElem e | nameString e == "DGLink" -> do
    l <- mkXLink e
    return sChgs { addLinks = l : addLinks sChgs }
  -- insert other child element will be processed within changeXml!
  _ -> fail "mkAddCh_fullElem"

-- determine the change(s) for a remove operation
mkRemoveCh :: Monad m => SimpleChanges -> Cursor -> Cursor -> m SimpleChanges
mkRemoveCh sChgs crInit crCurrent = case current crInit of
      -- remove entire node
      Elem e | nameString e == "DGNode" -> do
        nm <- liftM parseNodeName $ getAttrVal "name" e
        return sChgs { removeNodes = nm : removeNodes sChgs }
      -- remove entire link
      Elem e | nameString e == "DGLink" -> do
        ei <- readEdgeId_M e
        return sChgs { removeLinks = ei : removeLinks sChgs }
      -- remove child element -> update entire node or link
      _ -> mkUpdateCh sChgs crCurrent

mkUpdateCh :: Monad m => SimpleChanges -> Cursor -> m SimpleChanges
mkUpdateCh sChgs cr = case current cr of
    Elem e | nameString e == "DGNode" -> do
      n <- mkXNode e
      return sChgs { updateNodes = Map.insert (nodeName n) n
        $ updateNodes sChgs } 
    Elem e | nameString e == "DGLink" -> do
      l <- mkXLink e
      return sChgs { updateLinks = Map.insert (edgeId l) l
        $ updateLinks sChgs }
    _ -> maybe (fail "mkUpdateCh") (mkUpdateCh sChgs) $ parent cr

nameString :: Element -> String
nameString = qName . elName

readEdgeId_M :: Monad m => Element -> m EdgeId
readEdgeId_M e = do
  ei <- getAttrVal "EdgeId" e
  maybe (fail "readEdgeId_M") (return . EdgeId) $ readMaybe ei

