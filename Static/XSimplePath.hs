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

module Static.XSimplePath where

import Common.XPath hiding (Text)
import Common.XUpdate
import Common.Utils
import Common.GlobalAnnotations (GlobalAnnos)
import Common.Result (maybeResult)

import Control.Monad

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map

import Static.DgUtils
import Static.XGraph

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

data SimplePath = SimplePath { steps :: [Finder]
                             , changeData :: ChangeData }

{- Finder stores predicate list to locate the element and an index, in case
multiple elements comply with the predicate -}
data Finder = FindBy QName [Attr] Int

-- change to be applied at the end of a path plus (maybe) attr-selection
data ChangeData = ChangeData ChangeSel (Maybe String)

-- convert PathExpr into more simple Finder stucture
exprToSimplePath :: Monad m => Change -> m SimplePath
exprToSimplePath (Change csel e) = case e of
  PathExpr Nothing (Path True stps) -> do
    (fs, atS) <- foldM (\ (fs', atS') stp -> case stp of
        Step Child (NameTest n) exps -> do
          finder <- mkFinder (FindBy (unqual n) [] 1) exps
          return (finder : fs', atS')
        -- should be last step only. return path so-far plus attribute selector
        Step Attribute (NameTest n) [] -> return (fs', Just n)
        _ -> fail $ "unexpected step: " ++ show stp) ([], Nothing) stps
    return $ SimplePath (reverse fs) $ ChangeData csel atS
  _ -> fail $ "not a valid path description: " ++ show e

{- built Finder by recursively following Expr-structure and adding data to
an initially empty Finder along the way -}
mkFinder :: Monad m => Finder -> [Expr] -> m Finder
mkFinder = foldM mkFinderAux

mkFinderAux :: Monad m => Finder -> Expr -> m Finder
mkFinderAux f@(FindBy qn attrs i) e = case e of
    GenExpr True "and" es -> mkFinder f es
    GenExpr True "=" es -> do
      att <- mkAttr es
      return $ FindBy qn (att : attrs) i
    PrimExpr Number i' -> do
      v <- maybeF ("illegal number: " ++ i') $ readMaybe i'
      when (i /= 1) $ fail "XPATH number already set differently"
      return $ FindBy qn attrs v
    _ -> fail "unexpected (2)"

{- create attribute to locate the element with from expr-data.
this method will fail for many illegal expr-types! -}
mkAttr :: Monad m => [Expr] -> m Attr
mkAttr l = case l of
  [ PathExpr Nothing (Path False [Step Attribute (NameTest nm) []])
    , PrimExpr Literal val] -> return $ Attr (unqual nm) val
  _ -> fail $ "XPATH unexpected attr: " ++ show l

-- iterate Xml in multiple directions
data Direction = Vertical
               | Horizontal
               | TopElem

-- Remove-changes must be treated differently
data ChangeRes = ChangeCr Cursor
               | RemoveCr

-- Describes the minimal change-effect of a .diff upon a DGraph.
data DgEffect = DgEffect { removes :: Set.Set DgElemId
                         , updateNodes :: Map.Map NodeName XNode
                         , updateLinks :: Map.Map EdgeId XLink
                         , additions :: [XElem]
                         , updateAnnotations :: Maybe GlobalAnnos
                         , nextlinkid :: Int }

type DgElemId = Either NodeName EdgeId
type XElem = Either XNode XLink

instance Show DgEffect where
  show (DgEffect rmv updN updL [] Nothing _)
    | Set.null rmv && Map.null updN && Map.null updL = "No Effects!"
  show (DgEffect rmv updN updL adds annoCh _) = let
    showDgElemIds = unlines . map (showElems showName showEdgeId)
    showElems show' _ (Left a) = "Node: [" ++ show' a ++ "]"
    showElems _ show' (Right b) = "Link #" ++ show' b
    in (if Set.null rmv then "" else "<< Removes >>\n"
      ++ showDgElemIds (Set.toList rmv))
    ++ (if Map.null updN then "" else "<< Update Nodes >>\n"
      ++ unlines (map show (Map.elems updN)))
    ++ (if Map.null updL then "" else "<< Update Links >>\n"
       ++ unlines (map show (Map.elems updL)))
    ++ (if null adds then "" else "<< Insertions >>\n"
      ++ unlines (map (showElems show show) adds))
    ++ maybe "" (\ _ -> "Global Annotation Changed") annoCh

emptyDgEffect :: DgEffect
emptyDgEffect = DgEffect Set.empty Map.empty Map.empty [] Nothing (-1)

{- apply a diff to an xml-document. returns the result xml and a list of
changes that affect the original DGraph -}
changeXml :: Monad m => Element -> String -> m (Element, DgEffect)
changeXml el diff = let cr = fromElement el in do
  cs <- anaXUpdates diff
  pths <- mapM exprToSimplePath cs
  (cr', ef) <- iterateXml TopElem pths cr emptyDgEffect
  case current cr' of
     Elem e -> do
       -- the link-id needs to be updated here
       v <- readAttrVal "illegal nextlinkid" "nextlinkid" e
       return (e, ef { nextlinkid = v })
     _ -> fail "unexpected content within top element"

{- follow the Xml-structure and apply Changes. The Change is only applied after
the recursive call to simulate parallel application. Resulting DgChanges are
collected along the way. -}
iterateXml :: Monad m => Direction -> [SimplePath] -> Cursor
           -> DgEffect -> m (Cursor, DgEffect)
iterateXml _ [] cr ef = return (cr, ef)
iterateXml dir pths cr0 ef0 = do
  -- initially, the cursor movement has to be applied
  cr1 <- moveDown dir cr0
  (curChg, toRight, toChildren) <- propagatePaths cr1 pths
  (cr2, ef1) <- iterateXml Vertical toChildren cr1 ef0
  (cr3, ef2) <- iterateXml Horizontal toRight cr2 ef1
  -- after the call to children and rights, the current cursor is modified
  chRes <- applyChanges curChg cr3
  case chRes of
    ChangeCr cr4 -> do
      -- the changes are then extracted in a further, independent step
      ef3 <- mkAddOrUpdateCh cr4 curChg ef2
      crRes <- moveUp dir cr4
      return (crRes, ef3)
    RemoveCr -> do
      crRes <- case dir of
        Vertical -> maybeF "missing parent (Remove)" $ removeGoUp cr3
        Horizontal -> maybeF "missing left sibling (Remove)"
          $ removeFindLeft isElem cr3
        TopElem -> fail "Top Element cannot be removed!"
      ef3 <- mkRemoveCh ef2 cr3 crRes
      return (crRes, ef3)

removeFindLeft :: (Cursor -> Bool) -> Cursor -> Maybe Cursor
removeFindLeft p = maybe Nothing (\ cr ->
  if p cr then Just cr else findLeft p cr) . removeGoLeft

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
maybeF err = maybe (fail err) return

{- a list of Changes is applied to a current Cursor. If the Cursor is to be
removed, other changes will be ignored (and removal must take place within the
caller function). For other changes, the modified Element is returned.
NOTE: if new Elems are inserted, the returned Cursor will be the !leftmost! of
the resulting set of items. -}
applyChanges :: Monad m => [ChangeData] -> Cursor -> m ChangeRes
applyChanges changes cr = let
  -- because cursor position will change, certain addChanges are appended
  (chgAppend, chgNow) = partition (\ cd -> case cd of
    ChangeData (Add pos _) _ -> pos == Before
    _ -> False ) changes in do
  cres1 <- foldM applyChange (ChangeCr cr) chgNow
  foldM applyChange cres1 chgAppend

-- sequentially built up resulting Cursor one Change at a time
applyChange :: Monad m => ChangeRes -> ChangeData -> m ChangeRes
applyChange (RemoveCr) _ = return RemoveCr
applyChange (ChangeCr cr) (ChangeData csel attrSel) = case (csel, attrSel) of
  -- Case#1: full element removal
  (Remove, Nothing) -> return RemoveCr
  -- Case#2: attribute removal
  (Remove, Just atS) -> case current cr of
     Elem e -> return $ ChangeCr cr { current = Elem $
       e { elAttribs = filter ((/= atS) . qName . attrKey) $ elAttribs e } }
     _ -> fail "applyChange(remove-attr)"
  -- Case#3: addChanges, either attr-/ or element-insertion
  (Add pos addCs, _) -> liftM ChangeCr $ foldM (applyAddOp pos) cr addCs
  -- Case#4: update String (attr-only!)
  (Update s, Just atS) -> case current cr of
     Elem e -> return $ ChangeCr cr { current = Elem $
       e { elAttribs = map (\ at -> if qName (attrKey at) == atS
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
            Elem e' -> return cr { current = Elem $ e' {
                         elContent = Elem e : elContent e' } }
            _ -> fail "applyAddOp: unexpected content(1)"
        (Append, AddAttr at) -> case current cr of
            Elem e -> return cr { current = Elem $ add_attr at e }
            _ -> fail "applyAddOp: unexpected content(2)"
        _ -> fail "applyAddOp: illegal addChange-data!"

{- given the remaining PathElements, determine for which Paths the current
Cursor is relevant (else -> toRight) and then gather from those the changes
regarding the current object (PathEnds; else -> toChildren). -}
propagatePaths :: Monad m => Cursor -> [SimplePath]
               -> m ([ChangeData], [SimplePath], [SimplePath])
propagatePaths cr pths = case current cr of
  Elem e -> let
    checkAttr at = maybe False (== attrVal at) $ findAttr (attrKey at) e
    maybeDecrease sp = case steps sp of
          FindBy nm atL i : r | elName e == nm && all checkAttr atL
              -> sp { steps = FindBy nm atL (i - 1) : r }
          _ -> sp
    (cur, toRight) = partition isAtZero $ map maybeDecrease pths
            where isAtZero (SimplePath (FindBy _ _ 0 : _) _) = True
                  isAtZero _ = False
    in do
      -- crop current heads and extract immediate changes
      (changes, toChildren) <- foldM (\ (r1, r2) sp -> case sp of
          SimplePath [_] cd -> return (cd : r1, r2)
          SimplePath (_ : r) cd -> return (r1, SimplePath r cd : r2)
          _ -> fail "propagatePaths: unexpected PathEnd!") ([], []) cur
      return (changes, toRight, toChildren)
  c -> fail $ "propagatePaths: unexpected Cursor Content: " ++ show c

{- determine the effect of a remove operation. first see if the old (removed)
Elem was a Link or Node; if not, compute the update-change upon the new Elem.
-}
mkRemoveCh :: Monad m => DgEffect -> Cursor -> Cursor -> m DgEffect
mkRemoveCh ef crInit crNow = case current crInit of
      -- remove entire node
      Elem e | nameString e == "DGNode" -> do
        nm <- liftM parseNodeName $ getAttrVal "name" e
        return ef { removes = Set.insert (Left nm) $ removes ef }
      -- remove entire link
      Elem e | nameString e == "DGLink" -> do
        ei <- readEdgeId_M e
        return ef { removes = Set.insert (Right ei) $ removes ef }
      -- remove child element -> update entire node or link
      _ -> mkUpdateCh ef crNow

-- translates the Change data from the .diff into minimal DgChange-effects.
mkAddOrUpdateCh :: Monad m => Cursor -> [ChangeData] -> DgEffect -> m DgEffect
mkAddOrUpdateCh cr cs ef1 = do
  -- at first determine the element-additions
  (ef2, rl) <- foldM (\ (efR, r) cd -> case cd of
      ChangeData (Add pos adds) atS -> do
         (ef', r2) <- mkOnlyAddCh efR adds
         if null r2 then return (ef', r) else return
             (ef', ChangeData (Add pos r2) atS : r)
      c -> return (efR, c : r) ) (ef1, []) cs
  -- then only one update change is required for this position
  if null rl then return ef2 else mkUpdateCh ef2 cr

mkOnlyAddCh :: Monad m => DgEffect -> [AddChange] -> m (DgEffect, [AddChange])
mkOnlyAddCh ef' = foldM extractAddElems (ef', []) where
  extractAddElems (ef, r) addCh = case addCh of
    -- insert entire Node
    AddElem e | nameString e == "DGNode" -> do
      n <- mkXNode e
      return (ef { additions = Left n : additions ef }, r)
    -- insert entire link
    AddElem e | nameString e == "DGLink" -> do
      l <- mkXLink e
      return (ef { additions = Right l : additions ef }, r)
    _ -> return (ef, addCh : r)

-- determine which objects needs updating.
mkUpdateCh :: Monad m => DgEffect -> Cursor -> m DgEffect
mkUpdateCh ef cr = case current cr of
    Elem e | nameString e == "Global" ->
        case maybeResult $ parseAnnotations e of
          Just gl -> return $ ef { updateAnnotations = Just gl }
          Nothing -> fail "failed to parse global annotations"
    Elem e | nameString e == "DGNode" -> do
        nd <- mkXNode e
        return ef { updateNodes = Map.insert (nodeName nd) nd
                $ updateNodes ef }
    Elem e | nameString e == "DGLink" -> do
        lk <- mkXLink e
        return ef { updateLinks = Map.insert (edgeId lk) lk $ updateLinks ef }
    {- TODO: if no changeable item is found, the old effect-object is returned.
    all attribute changes on DGraph-level for example are lost! -}
    Elem e | nameString e == "DGraph" -> return ef
    _ -> maybe (fail "update failed, no updatable parent")
      (mkUpdateCh ef) $ parent cr

nameString :: Element -> String
nameString = qName . elName

readAttrVal :: (Read a, Monad m) => String -> String -> Element -> m a
readAttrVal err attr = (>>= maybeF err . readMaybe) . getAttrVal attr

readEdgeId_M :: Monad m => Element -> m EdgeId
readEdgeId_M = liftM EdgeId . readAttrVal "readEdgeId_M" "linkid"

