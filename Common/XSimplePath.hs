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

import Control.Monad

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

type SimplePath = [SimpleStep]

data SimpleStep = MkStepDown QName
                | FindByAttr [Attr]
                | FindByNumber Int

moveTo :: Monad m => Element -> Expr -> m Cursor
moveTo el e = let cr = fromElement el in do
  sPth <- exprToSimplePath e
  foldM (flip moveStep) cr sPth

exprToSimplePath :: Monad m => Expr -> m SimplePath
exprToSimplePath e = case e of
  PathExpr Nothing (Path True stps) -> concatMapM anaSteps stps
  _ -> fail "unexpected (1)"

anaSteps :: Monad m => Step -> m SimplePath
anaSteps stp = case stp of
  -- TODO is MkStepDown the same for Attributes also?
  Step Attribute (NameTest n) [] -> return [MkStepDown (unqual n)]
  Step Child (NameTest n) exps -> do
    atL <- if null exps then return []
             else do
               atL' <- mkAttrList exps
               return [FindByAttr atL']
    return $ MkStepDown (unqual n) : atL
  _ -> fail "unexpected (2)"


concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f

mkAttrList :: Monad m => [Expr] -> m [Attr]
mkAttrList [] = fail "unexpected (9)"
-- TODO do anything with the tail?
mkAttrList (e : _) = case e of
    GenExpr True "and" exp' -> concatMapM mkAttrList $ map (: []) exp'
    GenExpr True "=" exp' -> do
      at1 <- mkAttr exp'
      return [at1]
    -- TODO Would be <=> FindByNumber, but I think the information is redundant
    PrimExpr _ _ -> return []
    _ -> fail $ "unexpected (3)" ++ show e

mkAttr :: Monad m => [Expr] -> m Attr
mkAttr (e1 : e2 : r) = do
  unless (null r) $ fail "unexpected (8)"
  case e1 of
    PathExpr Nothing (Path False stps) -> case stps of
      Step Attribute (NameTest nm) [] : [] -> case e2 of
        -- TODO are attribute fields correct?
        PrimExpr Literal val -> return $ Attr (unqual nm) val
        _ -> fail "unexpected (4)"
      _ -> fail "unexpected (5)"
    _ -> fail "unexpected (6)"
mkAttr _ = fail "unexpected (7)"

-- TODO needs a lot of testing right here..
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
        ++ unlines (map show attrs)
  -- Case #3, not implemented TODO what to do with it? (cp. -> mkAttrList)
  FindByNumber i | i < 2 -> return cr
                 | otherwise -> case right cr of
                      Just cr' -> moveStep (FindByNumber (i-1)) cr'
                      Nothing -> fail "index out of bounds"
