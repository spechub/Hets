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

data SimpleChange = AddEl XElem
                  | RemoveEl ElFinder

type XElem = Either XNode XLink

data ElFinder = FindNode String
              | FindLink EdgeId

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
--  ?WHY DONT THIS WORK?    Just cr' -> fmap curry cr' $ getRemoveChange crInit cr'
    -- TODO what to do when inserting any first element of a kind??
    Add pos addCs -> do
      (cr', insf) <- case pos of
        -- TODO: append works on child level. check both other cases also!
        Append -> do
          cr' <- maybe (fail "changeXml.Append")
              return $ firstChild crInit
          return (rightMost cr', insertGoRight)
        After -> return (crInit, insertGoRight)
        Before -> return (crInit, insertGoLeft)
      foldM (\ (cr'', chgs) addCh -> case addCh of
        -- insert entire Node
        AddElem e | nameString e == "DGNode" -> do
          newEl <- mkXNode e
          return (insf (Elem e) cr'', AddEl (Left newEl) : chgs)
        -- insert entire link
        AddElem e | nameString e == "DGLink" -> do
          newEl <- mkXLink e
          return (insf (Elem e) cr'', AddEl (Right newEl) : chgs)
        -- insert other child element, update proper parent
        -- TODO if multiple elems are added, only one update change should be output!
        AddElem e -> do
          chg <- mkUpdateCh cr''
          return (insf (Elem e) cr'', chg ++ chgs)
        _ -> fail $ "no implementation for " ++ show addCh ) (cr', []) addCs
    _ -> fail $ "no implementation for " ++ show csel

-- determine the change(s) for a remove operation
getRemoveChange :: Monad m => Cursor -> Cursor -> m [SimpleChange]
getRemoveChange crInit crCur = case current crInit of
      -- remove entire node
      Elem e | nameString e == "DGNode" -> do
          nm <- getAttrVal "name" e
          return [RemoveEl $ FindNode nm]
      -- remove entire link
      Elem e | nameString e == "DGLink" -> do
          i <- getAttrVal "EdgeId" e
          ei <- readEdgeId i
          return [RemoveEl $ FindLink ei]
      -- remove child element -> update node
      _ -> mkUpdateCh crInit

mkUpdateCh :: Monad m => Cursor -> m [SimpleChange]
mkUpdateCh cr = case current cr of
    Elem e | nameString e == "DGNode" -> do
          nm <- getAttrVal "name" e
          newEl <- mkXNode e
          return [RemoveEl $ FindNode nm, AddEl $ Left newEl]
    Elem e | nameString e == "DGLink" -> do
          i <- getAttrVal "EdgeId" e
          ei <- readEdgeId i
          newEl <- mkXLink e
          return [RemoveEl $ FindLink ei, AddEl $ Right newEl]
    _ -> maybe (fail "mkUpdateCh") mkUpdateCh $ parent cr

readEdgeId :: Monad m => String -> m EdgeId
readEdgeId = maybe (fail "readEdgeId") (return . EdgeId) . readMaybe

nameString :: Element -> String
nameString = qName . elName

-- help function for case: (AddEl) Append
rightMost :: Cursor -> Cursor
rightMost cr = case right cr of
  Just cr' -> rightMost cr'
  Nothing -> cr
