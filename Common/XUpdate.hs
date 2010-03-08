{- |
Module      :  $Header$
Description :  analyse xml update input
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

collect xupdate information
-}

module Common.XUpdate where

import Common.XPath
import Common.ToXml

import Text.XML.Light

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

instance Show AddChange where
  show c = case c of
    AddElem e -> showElement e
    AddAttr a -> showAttr a
    AddText s -> show s
    AddComment s -> "<!--" ++ s ++ "-->"
    AddPI n s -> "<?" ++ n ++ " " ++ s ++ "?>"

data ChangeSel
  = Add AddChange
  | Remove
  | Update String
  | Rename String
  | Variable String

instance Show ChangeSel where
  show c = case c of
    Add a -> '\n' : show a
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
    Just e -> liftM concat $ mapM anaXUpdate $ elChildren e

{- the input element is expected to be one of

 xupdate:insert-before
 xupdate:insert-after
 xupdate:append
 xupdate:remove

insert and append are treated identically since order does not matter
We ignore xupdate:update as this is only used to update a range, currently.
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

getAttrVal :: String -> Element -> Maybe String
getAttrVal = findAttr . unqual

getSelectAttr :: Element -> Maybe String
getSelectAttr = getAttrVal "select"

getNameAttr :: Element -> Maybe String
getNameAttr = getAttrVal "name"

str2QName :: String -> QName
str2QName str = let (ft, rt) = break (== ':') str in
  case rt of
    _ : l@(_ : _) -> (unqual l) { qPrefix = Just ft }
    _ -> unqual str

anaXUpdate :: Monad m => Element -> m [Change]
anaXUpdate e = let q = elName e in
  if isXUpdateQN q then case getSelectAttr e of
    Nothing -> failX "missing select attribute" q
    Just sel -> case parseExpr sel of
      Left _ -> fail $ "unparsable xpath: " ++ sel
      Right p -> case () of
        _ | isAddQN q -> do
          cs <- mapM addXElem $ elChildren e
          let ps = getPaths p
          if all ((== TElement) . finalPrincipalNodeType) ps then
              return $ map (\ c -> Change (Add c) p) cs
            else fail $ "expecting element path: " ++ sel
          | isRemoveQN q ->
              return [Change Remove p]
          | hasLocalQN "variable" q -> case getNameAttr e of
              Nothing -> failX "expected name attribute" q
              Just vn -> return [Change (Variable vn) p]
        _ -> case lookup (qName q) [("update", Update), ("rename", Rename)] of
          Just c -> return [Change (c $ strContent e) p]
          Nothing -> failX "no xupdate modification" q
  else failX "no xupdate qualified element" q

partitionAddChanges :: [AddChange] -> ([Attr], [Content])
partitionAddChanges = foldr (\ c (as, cs) -> case c of
      AddAttr a -> (a : as, cs)
      AddElem e -> (as, Elem e : cs)
      AddText s -> (as, mkText s : cs)
      _ -> (as, cs)) ([], [])

failX :: Monad m => String -> QName -> m a
failX str q = fail $ str ++ ": " ++ showQName q

addXElem :: Monad m => Element -> m AddChange
addXElem e = let q = elName e in
  if isXUpdateQN q then case () of
      _ | isTextQN q -> return $ AddText $ strContent e
        | hasLocalQN "comment" q -> return $ AddComment $ strContent e
        | hasLocalQN "value-of" q -> failX "no support for" q
      _ -> case getNameAttr e of
        Just n -> let qn = str2QName n in case () of
          _ | isAttributeQN q ->
               return $ AddAttr $ Attr qn $ strContent e
            | isElementQN q ->  do
              es <- mapM addXElem $ elChildren e
              let (as, cs) = partitionAddChanges es
              return $ AddElem $ add_attrs as $ node qn cs
            | hasLocalQN pIS q -> return $ AddPI n $ strContent e
          _ -> failX "unknown change" q
        Nothing -> failX "missing name attribute for" q
  else failX "no xupdate element" q

{-
 xupdate:element
 xupdate:attribute
 xupdate:text

xupdate:element may contain xupdate:attribute elements and further
xupdate:element or xupdate:text elements.
 -}
