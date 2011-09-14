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

data SimpleChange = RemoveNode String
                  | RemoveLink EdgeId
                  | RenameNode String String
                  | RenumberLink EdgeId EdgeId
                  | UpdateNode XNode
                  | UpdateLink XLink
                  | AddNode XNode
                  | AddLink XLink

applyXmlDiff_improved :: Monad m => Element -> String
                      -> m (Element, [SimpleChange])
applyXmlDiff_improved = undefined

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = do
  cs <- anaXUpdates diff
  (cr, chgs) <- foldM changeXml (fromElement el, []) cs
  toElement cr

toElement :: Monad m => Cursor -> m Element
toElement cr = case current $ root cr of
    Elem e -> return e
    _ -> fail "cannot convert Cursor into Element"

removeAttr :: String -> Element -> Element
removeAttr atName el = el { elAttribs =
  filter ((/= atName) . qName . attrKey) $ elAttribs el }

changeXml :: Monad m => (Cursor, [SimpleChange]) -> Change
          -> m (Cursor, [SimpleChange])
changeXml (cr, sChgs) (Change csel expr) = do
  (crInit, attrSel) <- moveTo expr (root cr)
  case csel of
    Remove -> case attrSel of
      -- Case #1: remove attribute from element
      Just attr -> case current crInit of
        Elem e -> let e' = removeAttr attr e
                      cr' = cr { current = Elem e' } in do
          chg <- mkUpdateCh cr' 
          return (cr, chg : sChgs)
        _ -> fail "changeXml.RemoveAttr"
      -- Case #2: remove element
      Nothing -> case removeGoUp crInit of
        Nothing -> fail "changeXml.RemoveEl"
        Just cr' -> do
          chg <- mkRemoveCh crInit cr'
          return (cr', chg : sChgs)
    Add pos addCs -> case attrSel of
      -- Case #3: add attribute(s) to element
      -- TODO: implement, of course!
      Just attr -> undefined
      -- Case #4: add new elements
      Nothing -> do
        (cr', insf) <- case pos of
          {- TODO: append works on child level. check both other cases also!
          but: FIND BETTER SOLUTION! -}
          Append -> do
            cr' <- maybe (fail "changeXml.Append") return $ firstChild crInit
            return (rightMost cr', insertGoRight)
          After -> return (crInit, insertGoRight)
          Before -> return (crInit, insertGoLeft)
        crNew <- foldM (\ cr'' addCh -> case addCh of
                   AddElem e -> return $ insf (Elem e) cr''
                   AddAttr at -> case current cr'' of
                       Elem e -> return cr'' { current = Elem $ add_attr at e }
                       _ -> fail "changeXml.AddAttr"
                   _ -> fail $ "no implementation for " ++ show addCh) cr' addCs
        changes <- case mapM mkAddCh_fullElem addCs of
                   Just chList -> return chList
                   Nothing -> liftM ( :[] ) $ mkUpdateCh crNew
        return (crNew, changes ++ sChgs)
    -- TODO: I don't get it! whats the String for??
    Update s -> undefined
    _ -> fail $ "no implementation for :" ++ show csel


{- determine change for an add operation.
NOTE: this will purposfully fail for any other cases than add entire Node/Link!
-}
mkAddCh_fullElem :: Monad m => AddChange -> m SimpleChange
mkAddCh_fullElem addCh = case addCh of
  -- insert entire Node
  AddElem e | nameString e == "DGNode" -> liftM AddNode $ mkXNode e
  -- insert entire link
  AddElem e | nameString e == "DGLink" -> liftM AddLink $ mkXLink e
  -- insert other child element will be processed within changeXml!
  _ -> fail "mkAddCh_fullElem"

-- determine the change(s) for a remove operation
mkRemoveCh :: Monad m => Cursor -> Cursor -> m SimpleChange
mkRemoveCh crInit crCurrent = case current crInit of
      -- remove entire node
      Elem e | nameString e == "DGNode" -> liftM RemoveNode
            $ getAttrVal "name" e
      -- remove entire link
      Elem e | nameString e == "DGLink" -> do
        ei <- getAttrVal "EdgeId" e
        i <- readEdgeId_M ei
        return $ RemoveLink i
      -- remove child element -> update entire node or link
      _ -> mkUpdateCh crCurrent

mkUpdateCh :: Monad m => Cursor -> m SimpleChange
mkUpdateCh cr = case current cr of
    Elem e | nameString e == "DGNode" -> liftM UpdateNode $ mkXNode e
    Elem e | nameString e == "DGLink" -> liftM UpdateLink $ mkXLink e
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
