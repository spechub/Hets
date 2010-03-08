{- |
Module      :  $Header$
Description :  xml update input for Hets development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

adjust development graph according to xupdate information
-}

module Static.FromXml where

import Static.DevGraph

import Common.Result
import Common.XPath
import Common.ToXml

import Text.XML.Light

import Data.Either
import Data.List
import Data.Maybe

data Change = Change Element

anaUpdates :: LibEnv -> DGraph -> String -> Result [Change]
anaUpdates lenv dg input = case parseXMLDoc input of
    Nothing -> fail "cannot parse xupdate file"
    Just e -> fmap concat $ mapM (anaUpdate lenv dg) $ elChildren e

{- the input element is expected to be one of

 xupdate:insert-before
 xupdate:insert-after
 xupdate:append
 xupdate:remove

insert and append are treated identically since order does not matter
We ignore xupdate:update as this is only used to update a range, currently.
-}

isXUpdateQN :: QName -> Bool
isXUpdateQN = (Just "xupdate" ==) . qPrefix

hasLocalQN :: String -> QName -> Bool
hasLocalQN s = (== s) . qName

isElementQN :: QName -> Bool
isElementQN = hasLocalQN "element"

isAttributeQN :: QName -> Bool
isAttributeQN = hasLocalQN "attribute"

isTextQN :: QName -> Bool
isTextQN = hasLocalQN "text"

isAddQN :: QName -> Bool
isAddQN q = any (flip isPrefixOf $ qName q) ["insert", "append"]

isRemoveQN :: QName -> Bool
isRemoveQN = hasLocalQN "remove"

getAttrVal :: String -> Element -> Maybe String
getAttrVal = findAttr . unqual

getSelectVal :: Element -> String
getSelectVal = fromMaybe "" . getAttrVal "select"

getNameAttr :: Element -> Maybe String
getNameAttr = getAttrVal "name"

str2QName :: String -> QName
str2QName str = let (ft, rt) = break (== ':') str in
  case rt of
    _ : l@(_ : _) -> (unqual l) { qPrefix = Just ft }
    _ -> unqual str

anaUpdate :: LibEnv -> DGraph -> Element -> Result [Change]
anaUpdate l g e = let q = elName e in
  if isXUpdateQN q then
      if isAddQN q then
          case maybePath $ getSelectVal e of
            Just ex@(PathExpr _ (Path _ s@(_ : _)))
              | isPathExpr ex && isElementNode (last s) ->
                  mapM (anaAddElem l g) $ elChildren e
            _ -> fail $ "anaUpdate: " ++ showElement e
      else if isRemoveQN q then return [] else
          return [Change e]
  else return [Change e]

anaAddElem :: LibEnv -> DGraph -> Element -> Result Change
anaAddElem l g e = do
  r <- newXElem e
  case r of
    Left a -> fail $ "expecting element instead of attribute: " ++ showAttr a
      ++ "\n" ++ showElement e
    Right c -> case c of
      Elem xe -> return $ Change xe
      _ -> fail $ "unexpected text element: " ++ showElement e

newXElem :: Monad m => Element -> m (Either Attr Content)
newXElem e = let q = elName e in
  if isXUpdateQN q then
      if isTextQN q then return $ Right $ mkText $ strContent e
      else case getNameAttr e of
        Just n -> let qn = str2QName n in
          if isAttributeQN q then
               return $ Left $ Attr qn $ strContent e
          else if isElementQN q then do
            lrs <- mapM newXElem $ elChildren e
            let (as, cs) = partitionEithers lrs
            return $ Right $ Elem $ add_attrs as
              $ node qn $ cs
          else fail $ "no attribute or element: " ++ showElement e
        Nothing -> fail $ "missing name attribute: " ++ showElement e
  else fail $ "no xupdate element: " ++ showElement e

{-
 xupdate:element
 xupdate:attribute
 xupdate:text

xupdate:element may contain xupdate:attribute elements and further
xupdate:element or xupdate:text elements.
 -}
