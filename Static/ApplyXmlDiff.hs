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
  cr <- mkCursorAndMoveTo el expr
  case csel of
    Add pos addCs -> let
      ins = case pos of
              Before -> insertGoLeft
              _ -> insertGoRight
      {- TODO: for append, cursor needs to go to children level.
         check for other cases also! -}
      cr' = case pos of
              Append -> case firstChild cr of
                Just cr'' -> rightMost cr''
                Nothing -> error "changeXml(1)"
              _ -> cr
      cRes = foldl (\ crR cs -> case cs of
        AddElem e -> ins (Elem e) crR
        _ -> error $ "no implementation for " ++ show cs ) cr' addCs
      in toElement cRes
    Remove -> do
        cr' <- maybe (fail "removeGoUp") return $ removeGoUp cr
        toElement cr'
    _ -> fail $ "no implementation for " ++ show csel

rightMost :: Cursor -> Cursor
rightMost cr = case right cr of
  Just cr' -> rightMost cr'
  Nothing -> cr
