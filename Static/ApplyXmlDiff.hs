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
import Static.DgUtils (EdgeId (..))

import Common.XUpdate
import Common.XSimplePath
import Common.Utils (readMaybe)

import Control.Monad

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

-- ^ updates are combination of remove and add
data SimpleChange = RemoveNode String
                  | RemoveLink EdgeId
                  | AddNode XNode
                  | AddLink XLink

applyXmlDiff_improved :: Monad m => Element -> String
                      -> m (Element, [SimpleChange])
applyXmlDiff_improved = undefined

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = do
  cs <- anaXUpdates diff
  foldM (\ elR c -> do
         (cr', _) <- changeXml elR c
         toElement cr') el cs

toElement :: Monad m => Cursor -> m Element
toElement cr = case current $ root cr of
    Elem e -> return e
    _ -> fail "cannot convert Cursor into Element"

changeXml :: Monad m => Element -> Change
          -> m (Cursor, [SimpleChange])
changeXml el (Change csel expr) = do
  crInit <- mkCursorAndMoveTo el expr
  case csel of
    Remove -> case removeGoUp crInit of
      Nothing -> fail "changeXml.RemoveEl"
      Just cr' -> do
          chg <- getRemoveChange crInit cr'
          return (cr', chg)
{-  ?WHY DONT THIS WORK?    Just cr' -> fmap curry cr' $ getRemoveChange crInit cr' -}
    -- TODO what to do when inserting any first element of a kind??
    Add pos addCs -> do
      (cr', insf) <- case pos of
        -- TODO: append works on child level. check both other cases also!
        Append -> do
          cr' <- maybe (fail "changeXml.Append") return $ firstChild crInit
          return (rightMost cr', insertGoRight)
        After -> return (crInit, insertGoRight)
        Before -> return (crInit, insertGoLeft)
      crNew <- foldM (\ cr'' addCh -> case addCh of
                 AddElem e -> return $ insf (Elem e) cr''
              {- AddText s -> return $ insf (Text s) cr'' -}
                 _ -> fail $ "no implementation for " ++ show addCh) cr' addCs
      changes <- case mapM getAddElemChange addCs of
                   Just chList -> return chList
                   Nothing -> mkUpdateCh crNew
      return (crNew, changes)
    _ -> fail $ "no implementation for " ++ show csel

{- determine change for an add operation.
NOTE: this will purposfully fail for any other cases than add entire Node/Link!
-}
getAddElemChange :: Monad m => Functor m => AddChange -> m SimpleChange
getAddElemChange addCh = case addCh of
  -- insert entire Node
  AddElem e | nameString e == "DGNode" -> fmap AddNode $ mkXNode e
  -- insert entire link
  AddElem e | nameString e == "DGLink" -> fmap AddLink $ mkXLink e
  -- insert other child element will be processed within changeXml!
  _ -> fail "getAddElemChange"

-- determine the change(s) for a remove operation
getRemoveChange :: Monad m => Cursor -> Cursor -> m [SimpleChange]
getRemoveChange crInit crCurrent = case current crInit of
      -- remove entire node
      Elem e | nameString e == "DGNode" -> do
          nm <- getAttrVal "name" e
          return [RemoveNode nm]
      -- remove entire link
      Elem e | nameString e == "DGLink" -> do
          i <- getAttrVal "EdgeId" e
          ei <- readEdgeId_M i
          return [RemoveLink ei]
      -- remove child element -> update node
      _ -> mkUpdateCh crCurrent

mkUpdateCh :: Monad m => Cursor -> m [SimpleChange]
mkUpdateCh cr = case current cr of
    Elem e | nameString e == "DGNode" -> do
          nm <- getAttrVal "name" e
          newEl <- mkXNode e
          return [RemoveNode nm, AddNode newEl]
    Elem e | nameString e == "DGLink" -> do
          i <- getAttrVal "EdgeId" e
          ei <- readEdgeId_M i
          newEl <- mkXLink e
          return [RemoveLink ei, AddLink newEl]
    _ -> maybe (fail "mkUpdateCh") mkUpdateCh $ parent cr

readEdgeId_M :: Monad m => String -> m EdgeId
readEdgeId_M = maybe (fail "readEdgeId") (return . EdgeId) . readMaybe

nameString :: Element -> String
nameString = qName . elName

-- help function for case: (AddEl) Append
rightMost :: Cursor -> Cursor
rightMost cr = case right cr of
  Just cr' -> rightMost cr'
  Nothing -> cr
