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
printXmlDiff el diff = do
  cs <- anaXUpdates diff
  (_, chgs) <- foldM changeXml (fromElement el, emptyChanges) cs
  putStrLn $ show chgs

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = do
  cs <- anaXUpdates diff
  (cr, _) <- foldM changeXml (fromElement el, emptyChanges) cs
  toElement cr

toElement :: Monad m => Cursor -> m Element
toElement cr = case current $ root cr of
    Elem e -> return e
    _ -> fail "cannot convert Cursor into Element"

changeXml :: Monad m => (Cursor, SimpleChanges) -> Change
          -> m (Cursor, SimpleChanges)
changeXml (cr, sChgs) (Change csel expr) = do
  (crInit, attrSel) <- moveTo expr (root cr)
  case csel of
    Remove -> applyRemoveOp crInit attrSel sChgs
    Add pos addCs -> do
      crNew <- foldM (applyAddOp attrSel pos) crInit addCs 
      changes <- case foldM mkAddCh_fullElem sChgs addCs of
                   Just sChgs' -> return sChgs'
                   Nothing -> mkUpdateCh sChgs crNew
      return (crNew, changes)
    Update s -> case attrSel of
      Nothing -> fail "xupdate:update only works for Attributes!"
      Just atS -> do
        cr' <- case current crInit of
          Elem e -> return crInit { current = Elem
            $ add_attr (Attr (unqual atS) s) e }
          _ -> fail $ "update: " ++ s
        sChgs' <- mkUpdateCh sChgs cr'
        return (cr', sChgs')
    _ -> fail $ "no implementation for :" ++ show csel

applyRemoveOp :: Monad m => Cursor -> AttrSelector -> SimpleChanges
              -> m (Cursor, SimpleChanges)
applyRemoveOp crInit attrSel sChgs = case attrSel of
      -- Case #1: remove attribute from element
      Just attr -> case current crInit of
        Elem e -> let e' = removeAttr attr e
                      cr' = crInit { current = Elem e' } in do
          sChgs' <- mkUpdateCh sChgs cr'
          return (cr', sChgs')
        _ -> fail "applyRemoveOp (Attr)"
      -- Case #2: remove element
      Nothing -> case removeGoUp crInit of
        Nothing -> fail "applyRemoveOp (Elem)"
        Just cr' -> do
          sChgs' <- mkRemoveCh sChgs crInit cr'
          return (cr', sChgs')

removeAttr :: String -> Element -> Element
removeAttr atName el = el { elAttribs =
  filter ((/= atName) . qName . attrKey) $ elAttribs el }

applyAddOp :: Monad m => AttrSelector -> Insert -> Cursor -> AddChange
           -> m Cursor
applyAddOp attrSel pos cr addCh = case (pos, addCh, attrSel) of
        (Before, AddElem e, Nothing) -> return $ insertGoLeft (Elem e) cr
        (After, AddElem e, Nothing) -> return $ insertGoRight (Elem e) cr
        (Append, AddElem e, Nothing) -> case current cr of
            {- TODO: custem version of addChild, see if it works!! -}
            Elem e' -> return cr { current = Elem $ e' {
                         elContent = Elem e : elContent e' } }
            _ -> fail "applyAddOp(1)"
        -- TODO: there shouldn't be an attribute selection here, but there is!
        (Append, AddAttr at, _) -> case current cr of
            Elem e -> return cr { current = Elem $ add_attr at e }
            _ -> fail "applyAddOp(2)"
        _ -> fail "applyAddOp(3)"

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

