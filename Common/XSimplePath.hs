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
import Common.XUpdate

import Control.Monad

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

import Debug.Trace

type SimplePath = [SimpleStep]

data SimpleStep = MkStepDown QName
                | FindByAttr [Attr]
                | FindByNumber Int

readDiff :: String -> IO()
readDiff filepath = do
  xml <- readFile filepath
  cs <- anaXUpdates xml
  mapM_ (\ (Change _ e) -> case e of
    PathExpr Nothing (Path True stps) -> putStrLn $ show stps ++"\n\n"
    _ -> error "invalid pathexpr" ) cs
  --mapM (\ (Change _ e) -> exprToSimplePath e) cs

pathExprToSimplePath :: Monad m => Expr -> m SimplePath
pathExprToSimplePath e = case e of
  PathExpr Nothing (Path True stps) -> foldM (\ r stp -> case stp of
      Step Child (NameTest l) [] -> return $ MkStepDown (unqual l) : r
      Step Child (NameTest l) xs -> do
        es <- mapM convertExprAux xs
        return $ MkStepDown (unqual l) : (concat es) ++ r
      Step Attribute _ _ -> fail "found attributes" -- TODO: extract atribute list
      _ -> fail "exprToSimplePath: unexpected step") [] stps
  _ -> fail "exprToSimplePath (1)"

convertExprAux :: Monad m => Expr -> m SimplePath
convertExprAux e = undefined {-case e of
  GenExpr _ "and" args -> mapM convertExprAux args
  GenExpr _ "=" args -> case args of
    [PathExpr _ (Path _ stps1-}

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
