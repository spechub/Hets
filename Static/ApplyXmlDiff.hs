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

import Common.XUpdate
import Common.XPath

import Control.Monad

import Text.XML.Light

{-applyXmlDiffDG :: LibEnv -> LibName -> String -> DGraph
               -> ResultT IO (LibName, LibEnv)
applyXmlDiffDG = undefined -}

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = do
  cs <- anaXUpdates diff
  foldM changeXml el cs

changeXml :: Monad m => Element -> Change -> m Element
changeXml el (Change csel expr) = let
  -- TODO modChName :: Expr -> m QName
  modChName = undefined
  modChld = findChild modChName el
  -- TODO modify modChld
  chld' = undefined
  -- TODO reinsert chld into parent element
  in return el { elContent = chld' : elContent el }
