{- |
Module      :  ./Static/XSimplePath.hs
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

import Common.ToXml (mkText)
import Common.XPath hiding (Text)
import Common.XUpdate
import Common.Utils

import Control.Monad

import Data.List
import Data.Maybe
import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set

import Static.DgUtils
import Static.XGraph

import Text.XML.Light hiding (findChild)
import Text.XML.Light.Cursor

data SimplePath = SimplePath { steps :: [Finder]
                             , changeData :: ChangeData }

{- | Finder stores predicate list to locate the element and an index, in case
multiple elements comply with the predicate -}
data Finder = FindBy QName [Attr] Int

-- change to be applied at the end of a path plus (maybe) attr-selection
data ChangeData = ChangeData ChangeSel (Maybe String)

-- | convert PathExpr into more simple Finder stucture
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

{- | built Finder by recursively following Expr-structure and adding data to
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

{- | create attribute to locate the element with from expr-data. Note: this
method will fail for many illegal expr-types! -}
mkAttr :: Monad m => [Expr] -> m Attr
mkAttr l = case l of
  [ PathExpr Nothing (Path False [Step Attribute (NameTest nm) []])
    , PrimExpr Literal val] -> return $ Attr (unqual nm) val
  _ -> fail $ "XPATH unexpected attr: " ++ show l

-- | Describes the minimal change-effect of a .diff upon a DGraph.
data ChangeList = ChangeList
  { deleteNodes :: Set.Set NodeName
  , deleteLinks :: Set.Set XLink -- ^ stores additional information
  , changeNodes :: Map.HashMap NodeName ChangeAction
  , changeLinks :: Map.HashMap EdgeId ChangeAction } deriving (Eq, Show)

data ChangeAction = MkUpdate NodeMod | MkInsert deriving (Eq, Show)

updateNodeChange :: ChangeAction -> NodeName -> ChangeList -> ChangeList
updateNodeChange chA nm chL = chL { changeNodes =
  Map.insertWith mergeChA nm chA $ changeNodes chL }

retrieveNodeChange :: NodeName -> ChangeList
                   -> Maybe (ChangeAction, ChangeList)
retrieveNodeChange nm chL = do
  nmod <- Map.lookup nm $ changeNodes chL
  return (nmod, chL { changeNodes = Map.delete nm $ changeNodes chL })

updateLinkChange :: ChangeAction -> EdgeId -> ChangeList -> ChangeList
updateLinkChange chA ei chL = chL { changeLinks =
  Map.insertWith mergeChA ei chA $ changeLinks chL }

retrieveLinkChange :: EdgeId -> ChangeList -> Maybe (ChangeAction, ChangeList)
retrieveLinkChange ei chL = do
  nmod <- Map.lookup ei $ changeLinks chL
  return (nmod, chL { changeLinks = Map.delete ei $ changeLinks chL })

mergeChA :: ChangeAction -> ChangeAction -> ChangeAction
mergeChA (MkUpdate md1) (MkUpdate md2) = MkUpdate $ mergeNodeMod md1 md2
mergeChA _ _ = MkInsert

emptyChangeList :: ChangeList
emptyChangeList =
  ChangeList Set.empty Set.empty Map.empty Map.empty

-- | iterate Xml in multiple directions
data Direction = Vertical
               | Horizontal
               | TopElem

changeXml :: Monad m => Element -> String -> m (Element, ChangeList)
changeXml el input = case parseXMLDoc input of
    Nothing -> fail "changeXml: cannot parse xupdate file"
    Just diff -> changeXmlMod (cleanUpElem el) diff

{- | apply a diff to an xml-document. returns the result xml and a list of
changes that affect the original DGraph -}
changeXmlMod :: Monad m => Element -> Element -> m (Element, ChangeList)
changeXmlMod el diff = let cr = fromElement el in do
  cs <- anaMods diff
  pths <- mapM exprToSimplePath cs
  (cr', chL) <- iterateXml TopElem pths cr emptyChangeList
  case current cr' of
     Elem e -> return (e, chL)
     _ -> fail "unexpected content within top element"

{- | follow the Xml-structure and apply Changes. The Change is only applied
after the recursive call to simulate parallel application. Resulting DgChanges
are collected along the way. -}
iterateXml :: Monad m => Direction -> [SimplePath] -> Cursor
           -> ChangeList -> m (Cursor, ChangeList)
iterateXml _ [] cr chL = return (cr, chL)
iterateXml dir pths cr0 chL = do
  -- initially, the cursor movement has to be applied
  cr1 <- moveDown dir cr0
  (curChg, toRight, toChildren) <- propagatePaths cr1 pths
  (cr2, chL') <- iterateXml Vertical toChildren cr1 chL
  (cr3, chL'') <- iterateXml Horizontal toRight cr2 chL'
  -- after the call to children and rights, the current cursor is modified
  applyChanges curChg cr3 dir chL''

-- Remove-changes must be treated differently
data ChangeRes = ChangeCr Cursor
               | RemoveCr

{- | a list of Changes is applied to a current Cursor. The resulting DgUpdates
are added to the ChangeList. -}
applyChanges :: Monad m => [ChangeData] -> Cursor -> Direction -> ChangeList
             -> m (Cursor, ChangeList)
applyChanges changes cr dir chL = do
  -- to know the resulting DgUpdates, the Changes need not to be applied
  chL' <- foldM (updateChangeList cr) chL changes
  -- because cursor position will change, certain addChanges are appended
  let (chAppend, chNow) = partition (\ cd -> case cd of
          ChangeData (Add Before _) _ -> True
          _ -> False ) changes
  cres1 <- foldM applyChange (ChangeCr cr) chNow
  cres2 <- foldM applyChange cres1 chAppend
  -- after application of the changes, the Cursor movement takes place
  cr' <- case cres2 of
      ChangeCr cr' -> moveUp dir cr'
      RemoveCr -> case dir of
        Vertical -> maybeF "missing parent (Remove)" $ removeGoUp cr
        Horizontal -> maybeF "missing left sibling (Remove)"
          $ removeFindLeft isElem cr
        TopElem -> fail "Top Element cannot be removed!"
  return (cr', chL')

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

-- | sequentially built up resulting Cursor one Change at a time
applyChange :: Monad m => ChangeRes -> ChangeData -> m ChangeRes
applyChange (RemoveCr) _ = return RemoveCr
applyChange (ChangeCr cr) (ChangeData csel attrSel) = case (csel, attrSel) of
  -- Case#1: full element removal
  (Remove, Nothing) -> return RemoveCr
  -- Case#2: attribute removal
  (Remove, Just atS) -> removeOrChangeAttr Nothing cr atS
  -- Case#3: addChanges, either attr-/ or element-insertion
  (Add pos addCs, _) -> liftM ChangeCr $ foldM (applyAddOp pos) cr addCs
  -- Case#4: set attribute value
  (Update s, Just atS) -> removeOrChangeAttr (Just s) cr atS
  -- Case#5: update text-content
  (Update s, Nothing) -> changeText s cr
  -- OTHER CASES ARE NOT IMPLEMENTED!
  _ -> fail $ "no implementation for :" ++ show csel

-- | change the text-content of an element
changeText :: Monad m => String -> Cursor -> m ChangeRes
changeText t cr = case current cr of
  Elem e | null $ onlyElems $ elContent e -> return $ ChangeCr cr
    { current = Elem $ e
      { elContent = [mkText t] }}
  _ -> fail "current cursor is no element with text only"

-- | change or remove one of the elements attributes
removeOrChangeAttr :: Monad m => Maybe String -- ^ optional update value
  -> Cursor -> String -- ^ attribute key
  -> m ChangeRes
removeOrChangeAttr csel cr atS =
  let failMsg msg = fail $ "removeOrChangeAttr '" ++ atS ++ "': " ++ msg
  in case current cr of
  Elem e ->
    let (match, restAts) =
          partition ((== atS) . qName . attrKey) $ elAttribs e
    in case match of
      [at] -> return $ ChangeCr cr { current = Elem $ e
          { elAttribs = maybe [] (\ s -> [at { attrVal = s }]) csel
              ++ restAts } }
      [] -> failMsg "attribute not found"
      _ -> failMsg "ambiguous attribute"
  _ -> failMsg "current cursor is no element"

-- | add new elements or attributes
applyAddOp :: Monad m => Insert -> Cursor -> AddChange -> m Cursor
applyAddOp pos cr addCh = case (pos, addCh) of
        (Before, AddElem e) -> return $ insertGoLeft (Elem e) cr
        (After, AddElem e) -> return $ insertRight (Elem e) cr
        (Append, AddElem e) -> case current cr of
            Elem e' -> return cr { current = Elem $ e' {
                         elContent = elContent e' ++ [Elem e] } }
            _ -> fail "applyAddOp: unexpected content(1)"
        (Append, AddAttr at) -> case current cr of
            Elem e -> return cr { current = Elem $ add_attr at e }
            _ -> fail "applyAddOp: unexpected content(2)"
        _ -> fail "applyAddOp: illegal addChange-data!"

{- | given the remaining PathElements, determine for which Paths the current
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

{- | determine the required DgUpdates from a Change operation.
NOTE: some changes (like most attribute changes) will be ignored! -}
updateChangeList :: Monad m => Cursor -> ChangeList -> ChangeData
                 -> m ChangeList
updateChangeList cr chL (ChangeData csel atS) = case csel of
  Add _ addCs -> foldM (mkAddChange cr) chL addCs
  Remove | isNothing atS -> mkRemoveChange chL cr
  Update _ | isNothing atS -> case current cr of
    Elem e | isSentenceType e -> mkUpdateChange senMod chL cr
    Elem e | isSymbolType e -> mkUpdateChange symMod chL cr
    {- TODO: cases above have been considered and tested.
    Cases below will only receive update-information for reasons of fault-
    resistancy. They might be refined or even removed! -}
    _ -> mkUpdateChange symMod chL cr
  _ -> mkUpdateChange symMod chL cr

{- | split a list of AddChanges and write all Node and Link insertions into the
ChangeList. -}
mkAddChange :: Monad m => Cursor -> ChangeList -> AddChange -> m ChangeList
mkAddChange cr chL addCh = case addCh of
    AddElem e | isDgNodeElem e -> do
      nm <- extractNodeName e
      return $ updateNodeChange MkInsert nm chL
    AddElem e | isDgLinkElem e -> do
      ei <- extractEdgeId e
      return $ updateLinkChange MkInsert ei chL
    AddElem e | isSymbolType e -> mkUpdateChange addSymMod chL cr
    AddElem e | isSentenceType e -> mkUpdateChange addSenMod chL cr
    -- other cases as the above will be ignored
    _ -> return chL

-- | go upwards until an updatable element is found
mkUpdateChange :: Monad m => NodeMod -> ChangeList -> Cursor -> m ChangeList
mkUpdateChange nmod chL cr = case current cr of
  Elem e | isDgNodeElem e -> do
      nm <- extractNodeName e
      return $ updateNodeChange (MkUpdate nmod) nm chL
  Elem e | isDgLinkElem e -> do
      ei <- extractEdgeId e
      return $ updateLinkChange (MkUpdate nmod) ei chL
  -- if no updateable element is found, the change is ignored
  _ -> maybe (return chL) (mkUpdateChange nmod chL) $ parent cr

{- | if node or link is removed, add this to ChangeList. otherwise create
update-change -}
mkRemoveChange :: Monad m => ChangeList -> Cursor -> m ChangeList
mkRemoveChange chL cr = case current cr of
  Elem e | isDgNodeElem e -> do
      nm <- extractNodeName e
      return chL { deleteNodes = Set.insert nm $ deleteNodes chL }
  Elem e | isDgLinkElem e -> do
      xl <- mkXLink e
      return chL { deleteLinks = Set.insert xl $ deleteLinks chL }
  Elem e | isSymbolType e -> mkUpdateChange delSymMod chL cr
  Elem e | isAxiomType e -> mkUpdateChange delAxMod chL cr
  Elem e | isTheoremType e -> mkUpdateChange delThMod chL cr
  -- other cases as the above will be ignored
  _ -> return chL

nameStringIs :: String -> Element -> Bool
nameStringIs s = (== s) . qName . elName

isSymbolType :: Element -> Bool
isSymbolType e = nameStringIs "Symbol" e || nameStringIs "Declarations" e
  || nameStringIs "Hidden" e

isSentenceType :: Element -> Bool
isSentenceType e = isAxiomType e || isTheoremType e

isAxiomType :: Element -> Bool
isAxiomType e = nameStringIs "Axiom" e || nameStringIs "Axioms" e

isTheoremType :: Element -> Bool
isTheoremType e = nameStringIs "Theorem" e || nameStringIs "Theorems" e

isDgNodeElem :: Element -> Bool
isDgNodeElem = nameStringIs "DGNode"

isDgLinkElem :: Element -> Bool
isDgLinkElem = nameStringIs "DGLink"
