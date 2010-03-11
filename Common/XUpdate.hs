{- |
Module      :  $Header$
Description :  analyse xml update input
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

collect xupdate information
-}

module Common.XUpdate where

import Common.XPath
import Common.ToXml
import Common.Utils

import Text.XML.Light

import Data.Char
import Data.Either
import Data.List
import Data.Maybe

import Control.Monad

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

data Insert = Before | After | Append deriving Show

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

anaXUpdates :: Monad m => String -> m [Change]
anaXUpdates input = case parseXMLDoc input of
    Nothing -> fail "cannot parse xupdate file"
    Just e -> mapM anaXUpdate $ elChildren e

{- the input element is expected to be one of

 xupdate:insert-before
 xupdate:insert-after
 xupdate:append
 xupdate:remove
 xupdate:update
-}

isXUpdateQN :: QName -> Bool
isXUpdateQN = (Just "xupdate" ==) . qPrefix

hasLocalQN :: String -> QName -> Bool
hasLocalQN s = (== s) . qName

isElementQN :: QName -> Bool
isElementQN = hasLocalQN "element"

isAttributeQN :: QName -> Bool
isAttributeQN = hasLocalQN "attribute"

isTextQN :: QName -> Bool
isTextQN = hasLocalQN "text"

isAddQN :: QName -> Bool
isAddQN q = any (flip isPrefixOf $ qName q) ["insert", "append"]

isRemoveQN :: QName -> Bool
isRemoveQN = hasLocalQN "remove"

-- | extract the non-empty attribute value
getAttrVal :: Monad m => String -> Element -> m String
getAttrVal n e =
    (\ s -> if null s
            then failX ("missing " ++ n ++ " attribute") $ elName e
            else return s)
    . fromMaybe "" $ findAttr (unqual n) e

getSelectAttr :: Monad m => Element -> m String
getSelectAttr = getAttrVal "select"

getNameAttr :: Monad m => Element -> m String
getNameAttr = getAttrVal "name"

-- | convert a string to a qualified name by splitting at the colon
str2QName :: String -> QName
str2QName str = let (ft, rt) = break (== ':') str in
  case rt of
    _ : l@(_ : _) -> (unqual l) { qPrefix = Just ft }
    _ -> unqual str

-- | extract text and check for no other children
getText :: Monad m => Element -> m String
getText e = let s = trim $ strContent e in
  if null s then fail $ "empty text: " ++ showElement e else
  case elChildren e of
    [] -> return s
    c : _ -> failX "unexpected child" $ elName c

anaXUpdate :: Monad m => Element -> m Change
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
        _ -> case lookup u [("update", Update), ("rename", Rename)] of
          Just c -> do
            s <- getText e
            return $ Change (c s) p
          Nothing -> case lookup u $ map (\ i -> (showInsert i, i))
                     [Before, After, Append] of
            Just i -> do
              cs <- mapM addXElem $ elChildren e
              let ps = getPaths p
              if all ((== TElement) . finalPrincipalNodeType) ps then
                  return $ Change (Add i cs) p
                else fail $ "expecting element path: " ++ sel
            Nothing -> failX "no xupdate modification" q
  else failX "no xupdate qualified element" q

-- | partitions additions and ignores comments, pi, and value-of
partitionAddChanges :: [AddChange] -> ([Attr], [Content])
partitionAddChanges = foldr (\ c (as, cs) -> case c of
      AddAttr a -> (a : as, cs)
      AddElem e -> (as, Elem e : cs)
      AddText s -> (as, mkText s : cs)
      _ -> (as, cs)) ([], [])

failX :: Monad m => String -> QName -> m a
failX str q = fail $ str ++ ": " ++ showQName q

-- | check if the element contains no other content
noContent :: Monad m => Element -> a -> m a
noContent e a = case elContent e of
  [] -> return a
  c : _ -> fail $ "unexpected content: " ++ showContent c

addXElem :: Monad m => Element -> m AddChange
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
  else failX "no xupdate element" q

{-
xupdate:element
xupdate:attribute
xupdate:text

xupdate:element may contain xupdate:attribute elements and further
xupdate:element or xupdate:text elements.
-}
