{- |
Module      :  $Header$
Description :  Simplification of XPath-Structure
Copyright   :  (c) Simon Ulbricht, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  tekknix@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (DevGraph)

break down Common.XPath.Expr into a simpler path description and transfer
into cursor movement.
-}

module Common.XSimplePath where

import Common.XPath

import Control.Monad

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

type SimplePath = ([Finder], AttrSelector)

{- Finder stores predicate list to locate the element and an index, in case
multiple elements comply with the predicate -}
data Finder = FindBy QName [Attr] Int

type AttrSelector = Maybe String

moveTo :: Monad m => Expr -> Cursor -> m (Cursor, AttrSelector)
moveTo e cr = do
  (pth, attrSel) <- exprToSimplePath e
  case reverse pth of
    -- TODO: should empty path be allowed?
    [] -> return (cr, attrSel)
    (f : fs) -> do
      crInit <- findFromHere cr f
      crRes <- foldM (\ cr' f' -> case firstChild cr' of
        Nothing -> fail "no elChildren to follow the path"
        Just crDown -> findFromHere crDown f') crInit fs
      return (crRes, attrSel)

-- locate an Element according to Finder data
findFromHere :: Monad m => Cursor -> Finder -> m Cursor
findFromHere cr (FindBy qn attrs i) = let
  p1 = checkCursor qn attrs cr
  p2 = i <= 1
  -- could check if i runs below zero/one, but I don't
  i' = if p1 then i-1 else i
   in if p1 && p2 then return cr else case right cr of
      Just cr' -> findFromHere cr' $ FindBy qn attrs i'
      Nothing -> fail $ "couldn't locate desired Element: "
        ++ "\n type: " ++ show qn
        ++ (if null attrs then "" else "\n" ++ unlines (map show attrs))
        ++ "\n..no more right siblings to follow the path"

checkCursor :: QName -> [Attr] -> Cursor -> Bool
checkCursor nm atL cr = case current cr of
    Elem e -> elName e == nm && checkAttrs where
      checkAttrs = foldr (\ at r -> case findAttr (attrKey at) e of
                     Just atV -> atV == attrVal at && r
                     Nothing -> False) True atL
    _ -> False

-- convert PathExpr into more simple Finder stucture
exprToSimplePath :: Monad m => Expr -> m SimplePath
exprToSimplePath e = case e of
  PathExpr Nothing (Path True stps) -> foldM anaStep ([], Nothing) stps where
    anaStep (pth, at) stp = case stp of
        Step Child (NameTest n) exps -> do
          finder <- mkFinder (FindBy (unqual n) [] 1) exps
          return (finder : pth, at)
        -- should be last step only. return path so-far plus attribute selector
        Step Attribute (NameTest n) [] -> return (pth, Just n)
        _ -> fail $ "unexpected step: " ++ show stp
  _ -> fail $ "not a valid path description: " ++ show e

mkFinder :: Monad m => Finder -> [Expr] -> m Finder
mkFinder f [] = return f
mkFinder f@(FindBy qn attrs i) (e : r) = do
  f' <- case e of
    GenExpr True "and" es -> mkFinder f es
    GenExpr True "=" es -> do
      att <- mkAttr es
      return $ FindBy qn (att : attrs) i
    PrimExpr Number i' -> return $ FindBy qn attrs $ read i'
    _ -> fail "unexpected (2)"
  mkFinder f' r

{- create attribute to locate the element with from expr-data.
this method will fail for many illegal expr-types! -}
mkAttr :: Monad m => [Expr] -> m Attr
mkAttr [e1, e2] = case e1 of
    PathExpr Nothing (Path False stps) -> case stps of
      Step Attribute (NameTest nm) [] : [] -> case e2 of
        PrimExpr _ val -> return $ Attr (unqual nm) val
        _ -> fail "unexpected (4)"
      _ -> fail "unexpected (5)"
    _ -> fail "unexpected (6)"
mkAttr _ = fail "unexpected (7)"

