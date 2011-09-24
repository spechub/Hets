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
                | PathEnd ChangeData

{- Finder stores predicate list to locate the element and an index, in case
multiple elements comply with the predicate -}
data Finder = FindBy QName [Attr] Int

-- Change to be applied at the end of a path.
data ChangeData = ChangeData ChangeSel (Maybe String)

-- convert PathExpr into more simple Finder stucture
exprToSimplePath :: Monad m => Change -> m SimplePath
exprToSimplePath (Change csel e) = case e of
  PathExpr Nothing (Path True stps) -> anaSteps stps where
    anaSteps (stp : r) = case stp of
        Step Child (NameTest n) exps -> do
          finder <- mkFinder (FindBy (unqual n) [] 1) exps
          liftM (PathStep finder) $ anaSteps r
        -- should be last step only. return path so-far plus attribute selector
        Step Attribute (NameTest n) [] -> return $ PathEnd
               $ ChangeData csel $ Just n
        _ -> fail $ "unexpected step: " ++ show stp
    anaSteps [] = return $ PathEnd $ ChangeData csel Nothing
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

-- iterate Xml in multiple directions
data Direction = Vertical
               | Horizontal
               | TopElem

-- Remove-changes must be treated differently
data ChangeRes = ChangeCr Cursor
               | RemoveCr

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
  cr1 <- moveDown dir cr0
  (chgs, toRight, toChildren) <- propagatePaths cr1 pths
  cr2 <- iterateXml Vertical toChildren cr1
  cr3 <- iterateXml Horizontal toRight cr2
  chRes <- applyChanges chgs cr3
  case chRes of
    ChangeCr cr4 -> moveUp dir (findThisElem cr0) cr4
    RemoveCr -> case dir of
      Vertical -> maybeF "missing parent (Remove)" $ removeGoUp cr3
      Horizontal -> maybeF "missing left sibling (Remove)" $ removeGoLeft cr3
      TopElem -> fail "Top Element cannot be removed!"

moveDown :: Monad m => Direction -> Cursor -> m Cursor
moveDown dir cr = case dir of
    Vertical -> maybeF "no more children" $ findChild isElem cr
    Horizontal -> maybeF "no more right siblings" $ findRight isElem cr
    TopElem -> return cr

moveUp :: Monad m => Direction -> (Cursor -> Bool) -> Cursor -> m Cursor
moveUp dir p cr = case dir of
    Vertical -> maybeF "missing parent" $ parent cr
    Horizontal -> maybeF "missing left sibling" $ findLeft p cr
    TopElem -> return cr

findThisElem :: Cursor -> (Cursor -> Bool)
findThisElem cr cr' = case (current cr, current cr') of
  (Elem e, Elem e') -> elName e == elName e' && checkAttrs e (elAttribs e')
  _ -> False

-- help function for movement; filter out (Text CData)-Contents
isElem :: Cursor -> Bool
isElem cr = case current cr of
  Elem _ -> True
  _ -> False

maybeF :: Monad m => String -> Maybe a -> m a
maybeF err x = maybe (fail err) return x

-- TODO: for Remove-Element, all other changes are lost. is this desired?
applyChanges :: Monad m => [ChangeData] -> Cursor -> m ChangeRes
applyChanges pths cr = foldM applyChange (ChangeCr cr) pths

applyChange :: Monad m => ChangeRes -> ChangeData -> m ChangeRes
applyChange (RemoveCr) _ = return RemoveCr
applyChange (ChangeCr cr) (ChangeData csel attrSel) = case (csel, attrSel) of
  -- Case#1: full element removal
  (Remove, Nothing) -> return RemoveCr
  -- Case#2: attribute removal
  (Remove, Just atS) -> case current cr of
     Elem e -> return $ ChangeCr $ cr { current = Elem $
       e { elAttribs = filter ((/= atS) . qName . attrKey) $ elAttribs e } }
     _ -> fail "applyChange(remove-attr)"
  -- Case#3: addChanges, either attr-/ or element-insertion
  (Add pos addCs, _) -> liftM ChangeCr $ foldM (applyAddOp pos) cr addCs
  -- Case#4: update String (attr-only!)
  (Update s, Just atS) -> case current cr of
     Elem e -> return $ ChangeCr $ cr { current = Elem $
       e { elAttribs = map (\ at -> if (qName $ attrKey at) == atS
           then at { attrVal = s } else at) $ elAttribs e } }
     _ -> fail $ "applyChange(update): " ++ s
  -- OTHER CASES ARE NOT IMPLEMENTED!
  _ -> fail $ "no implementation for :" ++ show csel

applyAddOp :: Monad m => Insert -> Cursor -> AddChange
           -> m Cursor
applyAddOp pos cr addCh = case (pos, addCh) of
        (Before, AddElem e) -> return $ insertLeft (Elem e) cr
        (After, AddElem e) -> return $ insertRight (Elem e) cr
        (Append, AddElem e) -> case current cr of
            {- TODO: custem version of addChild, see if it works!! -}
            Elem e' -> return cr { current = Elem $ e' {
                         elContent = Elem e : elContent e' } }
            _ -> fail "applyAddOp(1)"
        (Append, AddAttr at) -> case current cr of
            Elem e -> return cr { current = Elem $ add_attr at e }
            _ -> fail "applyAddOp(2)"
        _ -> fail "applyAddOp(3)"

checkAttrs :: Element -> [Attr] -> Bool
checkAttrs e = all checkAttr where
   checkAttr at = case findAttr (attrKey at) e of
          Nothing -> False
          Just atV -> atV == attrVal at

propagatePaths :: Monad m => Cursor -> [SimplePath]
               -> m ([ChangeData], [SimplePath], [SimplePath]) 
propagatePaths cr pths = case current cr of
  Elem e -> let
    maybeDecrease pth = case pth of
              PathStep (FindBy nm atL i) r | elName e == nm && checkAttrs e atL
                -> PathStep (FindBy nm atL $ i-1) r
              st -> st
    (cur, toRight) = partition isAtZero $ map maybeDecrease pths
            where isAtZero (PathStep (FindBy _ _ 0) _) = True
                  isAtZero _ = False in do
      -- crop current heads and extract immediate changes
      (changes, toChildren) <- foldM (\ (r1, r2) c -> case c of
          PathStep _ rPth -> case rPth of
            PathEnd chDat -> return (chDat : r1, r2)
            st -> return (r1, st : r2)
          _ -> fail "unexpected PathEnd") ([], []) cur
      return (changes, toRight, toChildren)
  c -> fail $ "unexpected Cursor Content: " ++ show c

