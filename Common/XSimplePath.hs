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

import Common.XPath hiding (Text)
import Common.XUpdate

import Control.Monad

import Data.List

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

data SimplePath = PathStep Finder SimplePath
                | PathEnd ChangeSel (Maybe String)

{- Finder stores predicate list to locate the element and an index, in case
multiple elements comply with the predicate -}
data Finder = FindBy QName [Attr] Int

-- convert PathExpr into more simple Finder stucture
exprToSimplePath :: Monad m => Change -> m SimplePath
exprToSimplePath (Change csel e) = case e of
  PathExpr Nothing (Path True stps) -> anaSteps stps where
    anaSteps (stp : r) = case stp of
        Step Child (NameTest n) exps -> do
          finder <- mkFinder (FindBy (unqual n) [] 1) exps
          liftM (PathStep finder) $ anaSteps r
        -- should be last step only. return path so-far plus attribute selector
        Step Attribute (NameTest n) [] -> return $ PathEnd csel $ Just n
        _ -> fail $ "unexpected step: " ++ show stp
    anaSteps [] = return $ PathEnd csel Nothing
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

data Direction = Vertical
               | Horizontal
               | TopElem

changeXml :: Monad m => Element -> String -> m Element
changeXml el diff = let cr = fromElement el in do
  cs <- anaXUpdates diff
  pths <- mapM exprToSimplePath cs
  cr' <- iterateXml TopElem pths cr
  case current cr' of
     Elem e -> return e
     _ -> fail "unexpected content within top element"

iterateXml :: Monad m => Direction -> [SimplePath] -> Cursor -> m Cursor
iterateXml _ [] cr = return cr
iterateXml dir pths cr0 = do
  cr1 <- moveCursor dir cr0
  (chgs, toRight, toChildren) <- propagatePaths cr1 pths
  cr2 <- iterateXml Horizontal toRight cr1
  cr3 <- iterateXml Vertical toChildren cr2
  applyChanges dir chgs cr3

moveCursor :: Monad m => Direction -> Cursor -> m Cursor
moveCursor dir cr = case dir of
    Vertical -> maybe (fail "no more children") return
          $ findChild isElem cr
    Horizontal -> maybe (fail "no more right siblings") return
          $ findRight isElem cr
    TopElem -> return cr

isElem :: Cursor -> Bool
isElem cr = case current cr of
  Elem _ -> True
  _ -> False

-- TODO: using monadic return type to detect remove-Op, thus all error dialog is lost!
applyChanges :: Monad m => Direction -> [SimplePath] -> Cursor -> m Cursor
applyChanges dir pths cr = case foldM applyChange cr pths of
  Nothing -> case dir of
    Vertical -> maybe (fail "applyChanges(1)") return $ removeGoUp cr
    Horizontal -> maybe (fail "applyChanges(2)") return $ removeGoLeft cr
    TopElem -> fail "top element cannot be removed!"
  Just cr' -> case dir of
    Vertical -> maybe (fail "applyChanges(3)") return $ parent cr'
    Horizontal -> maybe (fail "applyChanges(4)") return $ findLeft isElem cr'
    TopElem -> return cr'

applyChange :: Monad m => Cursor -> SimplePath -> m Cursor
applyChange _ (PathStep _ _) = error "applyChange: unexpected remaining PathSteps"
applyChange cr (PathEnd csel attrSel) = case (csel, attrSel) of  
  (Remove, Nothing) -> fail "controlled failure: full element removal"
  (Remove, Just atS) -> case current cr of
     Elem e -> return cr { current = Elem $ e { elAttribs =
       filter ((/= atS) . qName . attrKey) $ elAttribs e } }
     _ -> error "applyChange(remove)"
  (Add pos addCs, _) -> foldM (applyAddOp pos) cr addCs
  (Update s, Just atS) -> case current cr of
     Elem e -> return cr { current = Elem $ add_attr (Attr (unqual atS) s) e }
     _ -> error $ "applyChange(update): " ++ s
  _ -> error $ "no implementation for :" ++ show csel

applyAddOp :: Monad m => Insert -> Cursor -> AddChange
           -> m Cursor
applyAddOp pos cr addCh = case (pos, addCh) of
        (Before, AddElem e) -> return $ insertGoLeft (Elem e) cr
        (After, AddElem e) -> return $ insertRight (Elem e) cr
        (Append, AddElem e) -> case current cr of
            {- TODO: custem version of addChild, see if it works!! -}
            Elem e' -> return cr { current = Elem $ e' {
                         elContent = Elem e : elContent e' } }
            _ -> error "applyAddOp(1)"
        -- TODO: there shouldn't be an attribute selection here, but there is!
        (Append, AddAttr at) -> case current cr of
            Elem e -> return cr { current = Elem $ add_attr at e }
            _ -> error "applyAddOp(2)"
        _ -> error "applyAddOp(3)"

propagatePaths :: Monad m => Cursor -> [SimplePath]
               -> m ([SimplePath], [SimplePath], [SimplePath]) 
propagatePaths cr pths = case current cr of
  -- TODO why does Text (CData) even occur?
--  Text _ -> maybe (fail "^,^") (`propagatePaths` pths) $ right cr
  Elem e -> let
    checkAttrs = all checkAttr
            where checkAttr at = case findAttr (attrKey at) e of
                    Nothing -> False
                    Just atV -> atV == attrVal at
    maybeDecrease pth = case pth of
              PathStep (FindBy nm atL i) r | elName e == nm && checkAttrs atL
                -> PathStep (FindBy nm atL $ i-1) r
              st -> st
    (cur, toRight) = partition isAtZero $ map maybeDecrease pths
            where isAtZero (PathStep (FindBy _ _ 0) _) = True
                  isAtZero _ = False
    isPathEnd (PathEnd _ _) = True
    isPathEnd _ = False
    tail' (PathStep _ rPth) = return rPth
    tail' (PathEnd _ _) = fail "unexpected PathEnd!" in do
      (changes, toChildren) <- liftM (partition isPathEnd) $ mapM tail' cur
      return (changes, toRight, toChildren)
  c -> fail $ "unexpected Cursor Content: " ++ show c

