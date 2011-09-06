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

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

type SimplePath = [Finder]

{- Finder stores predicate list to locate the element and an index, in case
multiple elements comply with the predicate -}
data Finder = FindBy QName [Attr] Int

-- create Cursor from Element and move towards PathExpr-position
moveTo :: Monad m => Element -> Expr -> m Cursor
moveTo el e = let cr = fromElement el in do
  sPth <- exprToSimplePath e
  moveToAux cr sPth

moveToAux :: Monad m => Cursor -> SimplePath -> m Cursor
moveToAux cr [] = return cr
moveToAux cr (FindBy nm atL i : stps) = do
  cr' <- findFromHere (checkCursor nm atL) cr
  case (i > 1, stps) of
    (False, []) -> return cr'
    -- if still steps left, move one level down and continue search
    (False, _) -> case firstChild cr' of
        Just cr'' -> moveToAux cr'' stps
        Nothing -> fail "no elChildren to follow the path"
    -- if counter >1, another element is wanted
    (True, _) -> case right cr' of
        Just cr'' -> moveToAux cr'' (FindBy nm atL (i-1) : stps)
        Nothing -> fail "no more right siblings to follow the path"

checkCursor :: QName -> [Attr] -> Cursor -> Bool
checkCursor nm atL cr = case current cr of
    Elem e -> elName e == nm && checkAttrs where
      checkAttrs = foldr (\ at r -> case findAttr (attrKey at) e of
                     Just atV -> atV == attrVal at && r
                     Nothing -> False) True atL
    _ -> False

findFromHere :: Monad m => (Cursor -> Bool) -> Cursor -> m Cursor
findFromHere p cr = if p cr then return cr else case right cr of
  Just cr' -> findFromHere p cr'
  Nothing -> fail "couldn't find desired element."

-- convert PathExpr into more simple Finder stucture
exprToSimplePath :: Monad m => Expr -> m SimplePath
exprToSimplePath e = case e of
  PathExpr Nothing (Path True stps) -> mapM anaSteps stps
  _ -> fail $ "not a valid path description: " ++ show e

anaSteps :: Monad m => Step -> m Finder
anaSteps stp = let basicFinder n = FindBy (unqual n) [] 1 in
  case stp of
    -- TODO: whats up with the attribute? why is it same as Child?
    Step Attribute (NameTest n) [] ->
      return $ basicFinder n
    Step Child (NameTest n) exps -> mkFinder (basicFinder n) exps
    _ -> fail "unexpected (1)"

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

mkAttr :: Monad m => [Expr] -> m Attr
mkAttr [e1, e2] = case e1 of
    PathExpr Nothing (Path False stps) -> case stps of
      Step Attribute (NameTest nm) [] : [] -> case e2 of
        -- TODO are attribute fields correct?
        PrimExpr _ val -> return $ Attr (unqual nm) val
        _ -> fail "unexpected (4)"
      _ -> fail "unexpected (5)"
    _ -> fail "unexpected (6)"
mkAttr _ = fail "unexpected (7)"

