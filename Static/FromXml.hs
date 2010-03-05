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

import Text.XML.Light

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

isAddQN :: QName -> Bool
isAddQN q = any (flip isPrefixOf $ qName q) ["insert", "append"]

isRemoveQN :: QName -> Bool
isRemoveQN q = qName q == "remove"

getAttrVal :: String -> Element -> Maybe String
getAttrVal = findAttr . unqual

getSelectVal :: Element -> String
getSelectVal = fromMaybe "" . getAttrVal "select"

anaUpdate :: LibEnv -> DGraph -> Element -> Result [Change]
anaUpdate l g e = let q = elName e in
  if isXUpdateQN q then
      if isAddQN q then
          case maybePath $ getSelectVal e of
            Just ex@(PathExpr _ (Path _ s@(_ : _)))
              | isPathExpr ex && isElementNode (last s) ->
                  fmap concat $ mapM (anaAddElem l g) $ elChildren e
            _ -> fail $ showElement e
      else if isRemoveQN q then return [] else
          return [Change e]
  else return [Change e]

anaAddElem :: LibEnv -> DGraph -> Element -> Result [Change]
anaAddElem l g e = let q = elName e in
  if isXUpdateQN q then undefined else undefined

{-
 xupdate:element
 xupdate:attribute

xupdate:element may contain further xupdate:element or xupdate:attribute
tags. Maybe xupdate:text can be ignored.
-}
