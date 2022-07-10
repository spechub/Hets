{- |
Module      :  ./Common/XUpdate.hs
Description :  analyse xml update input
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

collect xupdate information
<http://xmldb-org.sourceforge.net/xupdate/xupdate-wd.html>
<http://www.xmldatabases.org/projects/XUpdate-UseCases/>
-}

module Common.XUpdate where

import Common.XPath
import Common.ToXml
import Common.Utils

import Text.XML.Light as XML

import Data.Char
import Data.List

import Control.Monad
import qualified Control.Monad.Fail as Fail

-- | possible insertions
data AddChange
  = AddElem Element
  | AddAttr Attr
  | AddText String
  | AddComment String
  | AddPI String String
  | ValueOf

instance Show AddChange where
  show c = case c of
    AddElem e -> showElement e
    AddAttr a -> showAttr a
    AddText s -> show s
    AddComment s -> "<!--" ++ s ++ "-->"
    AddPI n s -> "<?" ++ n ++ " " ++ s ++ "?>"
    ValueOf -> valueOfS

valueOfS :: String
valueOfS = "value-of"

data Insert = Before | After | Append deriving (Eq, Show)

showInsert :: Insert -> String
showInsert i = let s = map toLower $ show i in case i of
  Append -> s
  _ -> "insert-" ++ s

data ChangeSel
  = Add Insert [AddChange]
  | Remove
  | Update String
  | Rename String
  | Variable String

instance Show ChangeSel where
  show c = case c of
    Add i cs -> showInsert i ++ concatMap (('\n' :) . show) cs
    Remove -> ""
    Update s -> '=' : s
    Rename s -> s
    Variable s -> '$' : s

data Change = Change ChangeSel Expr

instance Show Change where
  show (Change c p) =
    show p ++ ":" ++ show c

anaXUpdates :: Fail.MonadFail m => String -> m [Change]
anaXUpdates input = case parseXMLDoc input of
    Nothing -> Fail.fail "cannot parse xupdate file"
    Just e -> anaMods e

anaMods :: Fail.MonadFail m => Element -> m [Change]
anaMods = mapM anaXUpdate . elChildren

{- the input element is expected to be one of

 xupdate:insert-before
 xupdate:insert-after
 xupdate:append
 xupdate:remove
 xupdate:update
-}

xupdateS :: String
xupdateS = "xupdate"

updateS :: String
updateS = "update"

elementS :: String
elementS = "element"

attributeS :: String
attributeS = "attribute"

textS :: String
textS = "text"

appendS :: String
appendS = "append"

removeS :: String
removeS = "remove"

selectS :: String
selectS = "select"

isXUpdateQN :: QName -> Bool
isXUpdateQN = (Just xupdateS ==) . qPrefix

hasLocalQN :: String -> QName -> Bool
hasLocalQN s = (== s) . qName

isElementQN :: QName -> Bool
isElementQN = hasLocalQN elementS

isAttributeQN :: QName -> Bool
isAttributeQN = hasLocalQN attributeS

isTextQN :: QName -> Bool
isTextQN = hasLocalQN textS

isAddQN :: QName -> Bool
isAddQN q = any (flip isPrefixOf $ qName q) ["insert", appendS]

isRemoveQN :: QName -> Bool
isRemoveQN = hasLocalQN removeS

-- | extract the non-empty attribute value
getAttrVal :: Fail.MonadFail m => String -> Element -> m String
getAttrVal n e = case findAttr (unqual n) e of
  Nothing -> failX ("missing " ++ n ++ " attribute") $ elName e
  Just s -> return s

-- | apply a read operation to the extracted value
readAttrVal :: (Read a, Fail.MonadFail m) => String -> String -> Element -> m a
readAttrVal err attr = (>>= maybeF err . readMaybe) . getAttrVal attr

maybeF :: Fail.MonadFail m => String -> Maybe a -> m a
maybeF err = maybe (Fail.fail err) return

getSelectAttr :: Fail.MonadFail m => Element -> m String
getSelectAttr = getAttrVal selectS

getNameAttr :: Fail.MonadFail m => Element -> m String
getNameAttr = getAttrVal "name"

-- | convert a string to a qualified name by splitting at the colon
str2QName :: String -> QName
str2QName str = let (ft, rt) = break (== ':') str in
  case rt of
    _ : l@(_ : _) -> (unqual l) { qPrefix = Just ft }
    _ -> unqual str

-- | extract text and check for no other children
getText :: Fail.MonadFail m => Element -> m String
getText e = let s = trim $ strContent e in
  case elChildren e of
    [] -> return s
    c : _ -> failX "unexpected child" $ elName c

getXUpdateText :: Fail.MonadFail m => Element -> m String
getXUpdateText e = let
    msg = fail "expected single <xupdate:text> element"
    in case elChildren e of
  [] -> getText e
  [s] -> let
      q = elName s
      u = qName q
      in if isXUpdateQN q && u == "text" then getText s else msg
  _ -> msg

anaXUpdate :: Fail.MonadFail m => Element -> m Change
anaXUpdate e = let
  q = elName e
  u = qName q in
  if isXUpdateQN q then do
    sel <- getSelectAttr e
    case parseExpr sel of
      Left _ -> fail $ "unparsable xpath: " ++ sel
      Right p -> case () of
        _ | isRemoveQN q -> noContent e $ Change Remove p
          | hasLocalQN "variable" q -> do
              vn <- getNameAttr e
              noContent e $ Change (Variable vn) p
        _ -> case lookup u [(updateS, Update), ("rename", Rename)] of
          Just c -> do
            s <- getXUpdateText e
            return $ Change (c s) p
          Nothing -> case lookup u $ map (\ i -> (showInsert i, i))
                     [Before, After, Append] of
            Just i -> do
              cs <- mapM addXElem $ elChildren e
              return $ Change (Add i cs) p
            Nothing -> failX "no xupdate modification" q
  else failX "no xupdate qualified element" q

-- | partitions additions and ignores comments, pi, and value-of
partitionAddChanges :: [AddChange] -> ([Attr], [Content])
partitionAddChanges = foldr (\ c (as, cs) -> case c of
      AddAttr a -> (a : as, cs)
      AddElem e -> (as, Elem e : cs)
      AddText s -> (as, mkText s : cs)
      _ -> (as, cs)) ([], [])

failX :: Fail.MonadFail m => String -> QName -> m a
failX str q = Fail.fail $ str ++ ": " ++ showQName q

-- | check if the element contains no other content
noContent :: Fail.MonadFail m => Element -> a -> m a
noContent e a = case elContent e of
  [] -> return a
  c : _ -> Fail.fail $ "unexpected content: " ++ showContent c

addXElem :: Fail.MonadFail m => Element -> m AddChange
addXElem e = let q = elName e in
  if isXUpdateQN q then case () of
      _ | isTextQN q -> liftM AddText $ getText e
        | hasLocalQN "comment" q -> liftM AddComment $ getText e
        | hasLocalQN valueOfS q -> noContent e ValueOf
      _ -> do
        n <- getNameAttr e
        let qn = str2QName n
        case () of
          _ | isAttributeQN q ->
               liftM (AddAttr . Attr qn) $ getText e
            | isElementQN q -> do
              es <- mapM addXElem $ elChildren e
              let (as, cs) = partitionAddChanges es
              return $ AddElem $ add_attrs as $ node qn cs
            | hasLocalQN pIS q -> liftM (AddPI n) $ getText e
          _ -> failX "unknown change" q
  else return $ AddElem e

{-
xupdate:element
xupdate:attribute
xupdate:text

xupdate:element may contain xupdate:attribute elements and further
xupdate:element or xupdate:text elements.
-}

emptyCData :: CData -> Bool
emptyCData = all isSpace . cdData

validContent :: Content -> Bool
validContent c = case c of
  XML.Text t | emptyCData t -> False
  _ -> True

cleanUpElem :: Element -> Element
cleanUpElem e = e
  { elContent = map (\ c -> case c of
      Elem m -> Elem $ cleanUpElem m
      _ -> c) $ filter validContent $ elContent e }
