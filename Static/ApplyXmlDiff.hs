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
import Common.XSimplePath

import Control.Monad

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = do
  cs <- anaXUpdates diff
  foldM changeXml el cs

toElement :: Monad m => Cursor -> m Element
toElement cr = case current $ root cr of
    Elem e -> return e
    _ -> fail "cannot convert Cursor into Element"

changeXml :: Monad m => Element -> Change -> m Element
changeXml el (Change csel expr) = do
  cr <- moveTo el expr 
  case csel of
    Add pos addCs -> let
      ins = case pos of
              Before -> insertGoLeft
              After -> insertGoRight
              Append -> error "not implemented"
      insert' cr' c = case c of
        AddElem e -> return $ ins (Elem e) cr'
        _ -> fail $ "no implementation for " ++ show c
      in do
        cr' <- foldM insert' cr addCs
        toElement cr'
    Remove -> do
        cr' <- maybe (fail "removeGoUp") return $ removeGoUp cr
        toElement cr'
    _ -> fail $ "no implementation for " ++ show csel

