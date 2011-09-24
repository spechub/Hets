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
import Common.Utils

import Control.Monad

import Data.List
import qualified Data.Set as Set

import Static.DgUtils
import Static.XGraph

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

data DgEffect = DgEffect { removes :: Set.Set DgElemId
                         , updates :: Set.Set DgElemId
                         , addNodes :: [XNode]
                         , addLinks :: [XLink] }

instance Show DgEffect where
  show (DgEffect s1 s2 [] []) | Set.null s1 && Set.null s2 = "No Effects!"
  show (DgEffect rmv upd addN addL) =
    (if Set.null rmv then "" else "<< Removes>>\n" ++ showDgElemSet rmv)
    ++ (if Set.null upd then "" else "<< Updates >>\n" ++ showDgElemSet upd)
    ++ (if null addN then "" else "<< Node Insertion >>\n"
       ++ unlines (map show addN))
    ++ if null addL then "" else "<< Link Insertion >>\n "
       ++ unlines (map show addL)

type DgElemId = Either NodeName EdgeId

showDgElemSet :: Set.Set DgElemId -> String
showDgElemSet = unlines . map (\ e -> case e of
  Left nm -> "Node: " ++ show (getName nm)
  Right ei -> "Link: #" ++ show ei ) . Set.toList

emptyDgEffect :: DgEffect
emptyDgEffect = DgEffect Set.empty Set.empty [] []

changeXml :: Monad m => Element -> String -> m Element
changeXml el diff = let cr = fromElement el in do
  cs <- anaXUpdates diff
  pths <- mapM exprToSimplePath cs
  (cr', _) <- iterateXml TopElem pths cr emptyDgEffect
  case current cr' of
     Elem e -> return e
     _ -> fail "unexpected content within top element"

getEffect :: Monad m => Element -> String -> m DgEffect
getEffect el diff = let cr = fromElement el in do
  cs <- anaXUpdates diff
  pths <- mapM exprToSimplePath cs
  liftM snd $ iterateXml TopElem pths cr emptyDgEffect

iterateXml :: Monad m => Direction -> [SimplePath] -> Cursor -> DgEffect
           -> m (Cursor, DgEffect)
iterateXml _ [] cr ef = return (cr, ef)
iterateXml dir pths cr0 ef0 = do
  cr1 <- moveDown dir cr0
  (curChg, toRight, toChildren) <- propagatePaths cr1 pths
  (cr2, ef1) <- iterateXml Vertical toChildren cr1 ef0
  (cr3, ef2) <- iterateXml Horizontal toRight cr2 ef1
  (chRes, ef3) <- applyChanges curChg cr3 ef2
  let mkRetVal = liftM (\cr -> (cr, ef3))
  case chRes of
    ChangeCr cr4 -> mkRetVal $ moveUp dir cr4
    RemoveCr -> case dir of
      Vertical -> mkRetVal $ maybeF "missing parent (Remove)" $ removeGoUp cr3
      Horizontal -> mkRetVal $ maybeF "missing left sibling (Remove)"
              $ removeGoLeft cr3
      TopElem -> fail "Top Element cannot be removed!"

moveDown :: Monad m => Direction -> Cursor -> m Cursor
moveDown dir cr = case dir of
    Vertical -> maybeF "no more children" $ findChild isElem cr
    Horizontal -> maybeF "no more right siblings" $ findRight isElem cr
    TopElem -> return cr

moveUp :: Monad m => Direction -> Cursor -> m Cursor
moveUp dir cr = case dir of
    Vertical -> maybeF "missing parent" $ parent cr
    Horizontal -> maybeF "missing left sibling" $ findLeft isElem cr
    TopElem -> return cr

-- help function for movement; filter out (Text CData)-Contents
isElem :: Cursor -> Bool
isElem cr = case current cr of
  Elem _ -> True
  _ -> False

maybeF :: Monad m => String -> Maybe a -> m a
maybeF err x = maybe (fail err) return x

-- TODO: for Remove-Element, all other changes are lost. is this desired?
-- TODO: implement collection of DgEffect analogue to SimpleChange..
applyChanges :: Monad m => [ChangeData] -> Cursor -> DgEffect -> m (ChangeRes, DgEffect)
applyChanges changes cr ef = let
  -- because cursor position will change, certain addChanges are appended
  (chgNow, chgAppend) = partition (\ cd -> case cd of
    ChangeData (Add pos addCs) _ -> pos /= Append && any (\ ch -> case ch of
      AddElem _ -> True
      _ -> False ) addCs
    _ -> False ) changes in do
  cres1 <- foldM applyChange (ChangeCr cr) chgNow
  cres2 <- foldM applyChange cres1 chgAppend
  efRes <- determineDgEffect ef cr changes
  return (cres2, efRes)

determineDgEffect :: Monad m => DgEffect -> Cursor -> [ChangeData] -> m DgEffect
determineDgEffect ef0 cr cs = foldM updateEffect ef0 cs where
  updateEffect ef chgDat = case chgDat of
    ChangeData (Add _ addCs) _ -> case foldM mkAddCh_fullElem ef addCs of
        Nothing -> mkUpdateCh ef cr
        Just ef' -> return ef'
    ChangeData Remove Nothing -> mkRemoveCh ef cr
    _ -> mkUpdateCh ef cr
  
{- determine change for an add operation.
NOTE: this will purposfully fail for any other cases than add entire Node/Link!
-}
mkAddCh_fullElem :: Monad m => DgEffect -> AddChange -> m DgEffect
mkAddCh_fullElem ef addCh = case addCh of
  -- insert entire Node
  AddElem e | nameString e == "DGNode" -> do
    n <- mkXNode e
    return ef { addNodes = n : addNodes ef }
  -- insert entire link
  AddElem e | nameString e == "DGLink" -> do
    l <- mkXLink e
    return ef { addLinks = l : addLinks ef }
  -- insert other child element will be processed within changeXml!
  _ -> fail "mkAddCh_fullElem"

-- determine the change(s) for a remove operation
mkRemoveCh :: Monad m => DgEffect -> Cursor -> m DgEffect
mkRemoveCh ef cr = case current cr of
      -- remove entire node
      Elem e | nameString e == "DGNode" -> do
        nm <- liftM parseNodeName $ getAttrVal "name" e
        return ef { removes = Set.insert (Left nm) $ removes ef }
      -- remove entire link
      Elem e | nameString e == "DGLink" -> do
        ei <- readEdgeId_M e
        return ef { removes = Set.insert (Right ei) $ removes ef }
      -- remove child element -> update entire node or link
      _ -> mkUpdateCh ef cr

mkUpdateCh :: Monad m => DgEffect -> Cursor -> m DgEffect
mkUpdateCh ef cr = case current cr of
    Elem e | nameString e == "DGNode" -> do
        nm <- liftM parseNodeName $ getAttrVal "name" e
        return ef { updates = Set.insert (Left nm) $ updates ef }
    Elem e | nameString e == "DGLink" -> do
        ei <- readEdgeId_M e
        return ef { updates = Set.insert (Right ei) $ updates ef }
    _ -> maybe (fail "mkUpdateCh") (mkUpdateCh ef) $ parent cr

nameString :: Element -> String
nameString = qName . elName

readEdgeId_M :: Monad m => Element -> m EdgeId
readEdgeId_M e = do
  ei <- getAttrVal "EdgeId" e
  maybe (fail "readEdgeId_M") (return . EdgeId) $ readMaybe ei

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
        (Before, AddElem e) -> return $ insertGoLeft (Elem e) cr
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

