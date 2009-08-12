{- |
Module      :  $Header$
Description :  positions, simple and mixfix identifiers
Copyright   :  (c) Christian Maeder and Ewaryst Schulz and Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (multiple parameter class)

This module provides the item datatype for an abstract logic independent
representation of basic specs.

-}

module Common.Item where

import Data.Char

import Control.Monad.State
import Control.Applicative

import Common.Id
import Common.AS_Annotation

data ItemSubtype = No | Items | Decl | Defn | Free | Gen | Ext
                   deriving (Eq, Ord, Show)

data ItemKind = Datatype | SortK | Subsort | Var | Basic | Sig | Op | Pred
                deriving (Eq, Ord, Show)

data ItemType = Abstract String | Basicspec | IT ItemKind ItemSubtype
              | Simple ItemKind
              -- other keywords
              | Localvaraxioms | Axiomitems
              | Nonempty | Possiblyempty
                deriving (Eq, Ord, Show)

data Item = Item { itemType :: ItemType
                 , range :: Range
--                 , attribs :: [Item]
                 , items :: [Annoted Item]
                 } deriving (Eq, Ord, Show)


showIK :: ItemKind -> String
showIK SortK = "Sort"
showIK ik = show ik

hasValue :: ItemType -> Bool
hasValue (Abstract _) = True
hasValue _ = False

getName :: ItemType -> String
getName (Abstract _) = "Abstract"
getName (IT k s) =
    case s of Free -> "Free" ++ map toLower (showIK k)
              Ext  -> "Ext" ++ map toLower (showIK k)
              _ -> showIK k ++ map toLower (show s)
getName (Simple k) = showIK k ++ "item"
getName it = show it

getValue :: ItemType -> String
getValue (Abstract s) = s
getValue _ = ""


instance GetRange Item where
    getRange = range

{-
 In the following we use these abbreviations:
  I  = Item
  AI = Annoted Item
  IT = ItemType or ItemTypeable
-}

-- often we have the situation where we want to obtain an ItemType
-- from a certain Type:
class ItemTypeable a where
    toIT :: a -> ItemType

instance ItemTypeable ItemType where
    toIT = id

class Monad m => ItemConvertible a m where
    toitem :: a -> m Item


---------------------------- Sublist creation ----------------------------

listfromAList :: ItemConvertible a m => [Annoted a] -> m [Annoted Item]
listfromAList = mapM annToAItem

listfromList :: ItemConvertible a m =>
                (Item -> Annoted Item) -> [a] -> m [Annoted Item]
listfromList f = mapM (toAItem f)

annToAItem :: ItemConvertible a m => Annoted a -> m (Annoted Item)
annToAItem v = toitem (item v) >>= return . (<$ v)

toAItem :: ItemConvertible a m =>
           (Item -> Annoted Item) -> a -> m (Annoted Item)
toAItem f x = toitem x >>= return . f


---------------------------- ItemType lifting ----------------------------

-- often we have the situation where we want to obtain a whole Item
-- or even an Annoted Item from an ItemType:
liftIT2I :: ItemTypeable a => a -> Item
liftIT2I t = mkItem t nullRange []
liftIT2AI :: ItemTypeable a => a -> Annoted Item
liftIT2AI = emptyAnno . liftIT2I

---------------------------- Combinators ----------------------------

fromC :: ItemConvertible a m => a -> m (Annoted Item)
fromC = fromAC . emptyAnno

fromAC :: ItemConvertible a m => Annoted a -> m (Annoted Item)
fromAC = annToAItem

fromL :: (ItemConvertible a m, ItemTypeable b) => b -> [a] -> m (Annoted Item)
fromL it l =
    do{ l' <- listfromList emptyAnno l
      ; let i = liftIT2I it
      ; return $ emptyAnno i{ items = l' } }

fromAL :: (ItemConvertible a m, ItemTypeable b) => b -> [Annoted a] ->
          m (Annoted Item)
fromAL it l =
    do{ l' <- listfromAList l
      ; let i = liftIT2I it
      ; return $ emptyAnno i{ items = l' } }

---------------------------- standard items ----------------------------

rootItem :: Item
rootItem = liftIT2I Basicspec

abstract :: String -> Item
abstract = liftIT2I . Abstract

mkItem :: ItemTypeable a => a -> Range -> [Annoted Item] -> Item
mkItem it = Item (toIT it)
