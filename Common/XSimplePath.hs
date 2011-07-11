{- |
Module      :  $Header$
Description :  Simplification of XPath-Structure
Copyright   :  (c) Simon Ulbricht, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (DevGraph)

break down Common.XPath.Expr into a very simple path description.
-}

module Common.XSimplePath where

import Common.XPath

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

type SimplePath = [SimpleStep]

data SimpleStep = MkStepDown QName
                | FindByAttr [Attr]
                | FindByNumber Int

-- TODO:
exprToSimplePath :: Monad m => Expr -> m SimplePath
exprToSimplePath = undefined

moveStep :: Monad m => SimpleStep -> Cursor -> m Cursor
moveStep stp cr = case stp of
  -- Case #1
  MkStepDown nm -> let
    checkName nm' cr' = case current cr' of
      Elem e -> elName e == nm'
      _ -> False
    in case findChild (checkName nm) cr of
      Just cr' -> return cr'
      Nothing -> fail $ "cannot find any childs with name " ++ show nm
  -- Case #2
  FindByAttr attrs -> let
    checkAttrs attrs' cr' = case current cr' of
      Elem e -> foldr (\ at r -> case findAttr (attrKey at) e of
                  Nothing -> False
                  Just atV -> atV == attrVal at && r) True attrs'
      _ -> False
    in case findRight (checkAttrs attrs) cr of
      Just cr' -> return cr'
      Nothing -> fail $
        "cannot find an element that complies with the attributes: "
        ++ (unlines $ map show attrs)
  -- Case #3, not implemented
  FindByNumber _ -> fail "no implementation for FindByNumber"
