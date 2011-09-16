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
                  deriving Show

printXmlDiff :: Element -> String -> IO ()
printXmlDiff el diff = do
  cs <- anaXUpdates diff
  (cr, chgs) <- foldM changeXml (fromElement el, []) cs
  putStrLn $ unlines $ map show chgs

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = do
  cs <- anaXUpdates diff
  (cr, chgs) <- foldM changeXml (fromElement el, []) cs
  toElement cr

toElement :: Monad m => Cursor -> m Element
toElement cr = case current $ root cr of
    Elem e -> return e
    _ -> fail "cannot convert Cursor into Element"

changeXml :: Monad m => (Cursor, [SimpleChange]) -> Change
          -> m (Cursor, [SimpleChange])
changeXml (cr, sChgs) (Change csel expr) = do
  (crInit, attrSel) <- moveTo expr (root cr)
  case csel of
    Remove -> do
      (cr', chg) <- applyRemoveOp crInit attrSel
      return (cr', chg : sChgs)
    Add pos addCs -> do
      crNew <- applyAddOp attrSel pos crInit addCs 
      changes <- case mapM mkAddCh_fullElem addCs of
                   Just chList -> return chList
                   Nothing -> liftM ( :[] ) $ mkUpdateCh crNew
      return (crNew, changes ++ sChgs)
    -- TODO: I don't get it! whats the String for??
    Update s -> undefined
    _ -> fail $ "no implementation for :" ++ show csel

applyRemoveOp :: Monad m => Cursor -> AttrSelector -> m (Cursor, SimpleChange)
applyRemoveOp crInit attrSel = case attrSel of
      -- Case #1: remove attribute from element
      Just attr -> case current crInit of
        Elem e -> let e' = removeAttr attr e
                      cr' = crInit { current = Elem e' } in do
          chg <- mkUpdateCh cr' 
          return (cr', chg)
        _ -> fail "applyRemoveOp (Attr)"
      -- Case #2: remove element
      Nothing -> case removeGoUp crInit of
        Nothing -> fail "applyRemoveOp (Elem)"
        Just cr' -> do
          chg <- mkRemoveCh crInit cr'
          return (cr', chg)

removeAttr :: String -> Element -> Element
removeAttr atName el = el { elAttribs =
  filter ((/= atName) . qName . attrKey) $ elAttribs el }

applyAddOp :: Monad m => AttrSelector -> Insert -> Cursor -> [AddChange]
           -> m Cursor
applyAddOp attrSel pos = foldM (\ cr' addCh -> case (pos, addCh, attrSel) of
        (Before, AddElem e, Nothing) -> return $ insertGoLeft (Elem e) cr' 
        (After, AddElem e, Nothing) -> return $ insertGoRight (Elem e) cr'
        (Append, AddElem e, Nothing) -> case current cr' of
            {- TODO: custem version of addChild, see if it works!! -}
            Elem e' -> return cr' { current = Elem $ e' {
                         elContent = Elem e : elContent e' } }
            _ -> fail "applyAddOp(1)"
        (Before, AddAttr at, Just atSel) -> insertAttr cr' (Left atSel) at
        (After, AddAttr at, Just atSel) -> insertAttr cr' (Right atSel) at
        (Append, AddAttr at, Nothing) -> case current cr' of
            Elem e -> return cr' { current = Elem $ add_attr at e }
            _ -> fail "applyAddOp(2)"
        _ -> fail "applyAddOp(3)"                              )

{- insert an attribute at a specific location.
TODO: if attribute-selector is not found, nothing happens. no safeguard.. -}
insertAttr :: Monad m => Cursor -> Either String String -> Attr -> m Cursor
insertAttr cr atSel at = case current cr of
  Elem e -> return cr { current = Elem $ e { elAttribs = foldr (\ at' atR ->
    case atSel of
      Left atS | (qName $ attrKey at') == atS -> at : at' : atR
      Right atS | (qName $ attrKey at') == atS -> at' : at : atR
      _ -> at' : atR ) [] $ elAttribs e } }
  _ -> fail "insertAttr"

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
      Elem e | nameString e == "DGLink" -> liftM RemoveLink
            $ readEdgeId_M e
      -- remove child element -> update entire node or link
      _ -> mkUpdateCh crCurrent

mkUpdateCh :: Monad m => Cursor -> m SimpleChange
mkUpdateCh cr = case current cr of
    Elem e | nameString e == "DGNode" -> liftM UpdateNode $ mkXNode e
    Elem e | nameString e == "DGLink" -> liftM UpdateLink $ mkXLink e
    _ -> maybe (fail "mkUpdateCh") mkUpdateCh $ parent cr

nameString :: Element -> String
nameString = qName . elName

readEdgeId_M :: Monad m => Element -> m EdgeId
readEdgeId_M e = do
  ei <- getAttrVal "EdgeId" e
  maybe (fail "readEdgeId_M") (return . EdgeId) $ readMaybe ei

