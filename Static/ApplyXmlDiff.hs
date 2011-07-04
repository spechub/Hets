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
import Common.XPath (Expr (..), Step (..), Axis (..), NodeTest (..), Path (..)
  , showSteps)

import Control.Monad

import Text.XML.Light
import Text.XML.Light.Cursor (Cursor (..))
import qualified Text.XML.Light.Cursor as Cr (fromElement, findChild)

applyXmlDiff :: Monad m => Element -> String -> m Element
applyXmlDiff el diff = do
  cs <- anaXUpdates diff
  foldM changeXml el cs

changeXml :: Monad m => Element -> Change -> m Element
changeXml el (Change csel expr) = case csel of
    Add _ addCs -> foldM insertXml el addCs where
      insertXml e' c = case c of
        AddElem e -> return e' { elContent = Elem e : elContent e' }
        _ -> fail $ "no implementation for " ++ show c
    Remove -> undefined
    _ -> fail $ "no implementation for " ++ show csel

cursorFromPathExpr :: Monad m => Expr -> Element -> m Cursor
cursorFromPathExpr expr el = case expr of
  PathExpr Nothing (Path False (stp : stps)) -> do
    unless (checkStepElement "DGraph" stp)
      $ fail "unexpected step"
    cr <- findChildByName "input is not a DGraph element" (unqual "DGraph")
            $ Cr.fromElement el
    anaSteps cr stps
  _ -> fail $ "no implementation for expression: " ++ show expr

checkStepElement :: String -> Step -> Bool
checkStepElement str stp = case stp of
  Step Child (NameTest l) _ | l == str -> True
  _ -> False

findChildByName :: Monad m => String -> QName -> Cursor -> m Cursor
findChildByName err qNm cr = case Cr.findChild ( \c -> case current c of
            Elem e -> elName e == qNm
            _ -> False ) cr of
    Nothing -> fail err
    Just cr' -> return cr'

anaSteps :: Monad m => Cursor -> [Step] -> m Cursor
anaSteps cr stps = case stps of
  Step Child (NameTest l) _ : stps' -> do
    cr' <- findChildByName "unexpected step(2)" (unqual l) cr
    anaSteps cr' stps'
  [] -> return cr
  _ -> fail $ "no implementation for " ++ showSteps False stps

removeXml :: (Element -> Bool) -> Element -> Element
removeXml f e = let ct = elContent e in
  e { elContent = foldr (\ c cs -> case c of
        Elem e' -> if f e' then cs else (Elem e') : cs
        _ -> c : cs ) [] ct }


