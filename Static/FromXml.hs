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

import Text.XML.Light

import Data.List

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

anaUpdate :: LibEnv -> DGraph -> Element -> Result [Change]
anaUpdate l g e = let q = elName e in
  if isXUpdateQN q then
      if isAddQN q then anaAddElems l g $ elChildren e else
      if isRemoveQN q then return [] else
          return [Change e]
  else return [Change e]

anaAddElems :: LibEnv -> DGraph -> [Element] -> Result [Change]
anaAddElems = undefined

{-
 xupdate:element
 xupdate:attribute

xupdate:element may contain further xupdate:element or xupdate:attribute
tags. Maybe xupdate:text can be ignored.
-}
