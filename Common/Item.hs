{-# LANGUAGE MultiParamTypeClasses #-}
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

data ItemType = IT [String]
              
                deriving (Eq, Ord, Show)


--- flat items (isFlat=True) are intended for output as xml-attributes
--- but this is not yet used
data Item = Item { itemType :: ItemType
                 , isFlat :: Bool
                 , range :: Range
--                 , attribs :: [Item]
                 , items :: [Annoted Item]
                 } deriving (Eq, Ord, Show)

hasValue :: ItemType -> Bool
hasValue (IT l) = length l > 1

getName :: ItemType -> String
getName (IT (h:_)) = h
getName _ = "GEN_ItemType"

getValue :: ItemType -> String
getValue (IT []) = ""
getValue (IT l) = last l

getValueName :: ItemType -> String
getValueName (IT [_,v,_]) = v
getValueName (IT _) = "value"

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

-- intelligent ItemType generation
instance ItemTypeable String where
    toIT s = IT [s]
instance ItemTypeable (String, String) where
    toIT (s,s') = IT [s,s']
instance ItemTypeable (String, String, String) where
    toIT (s,s',s'') = IT [s,s',s'']



class Monad m => ItemConvertible a m where
    toitem :: a -> m Item


---------------------------- Sublist creation ----------------------------

listFromAL :: ItemConvertible a m => [Annoted a] -> m [Annoted Item]
listFromAL = mapM annToAItem

listFromLWithA :: ItemConvertible a m =>
                  (Item -> Annoted Item) -> [a] -> m [Annoted Item]
listFromLWithA f = mapM (toAItemWithA f)

listFromL :: ItemConvertible a m => [a] -> m [Annoted Item]
listFromL = mapM toAItem

annToAItem :: ItemConvertible a m => Annoted a -> m (Annoted Item)
annToAItem v = toitem (item v) >>= return . (<$ v)

toAItemWithA :: ItemConvertible a m =>
           (Item -> Annoted Item) -> a -> m (Annoted Item)
toAItemWithA f x = toitem x >>= return . f

toAItem :: ItemConvertible a m => a -> m (Annoted Item)
toAItem = toAItemWithA emptyAnno


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
    do{ l' <- listFromL l
      ; let i = liftIT2I it
      ; return $ emptyAnno i{ items = l' } }

fromAL :: (ItemConvertible a m, ItemTypeable b) => b -> [Annoted a] ->
          m (Annoted Item)
fromAL it l =
    do{ l' <- listFromAL l
      ; let i = liftIT2I it
      ; return $ emptyAnno i{ items = l' } }

---------------------------- standard items ----------------------------

rootItem :: Item
rootItem = liftIT2I "Basicspec"

mkItem :: ItemTypeable a => a -> Range -> [Annoted Item] -> Item
mkItem it = Item (toIT it) False

mkFlatItem :: ItemTypeable a => a -> Range -> Item
mkFlatItem it rg = Item (toIT it) True rg []

mkItemM :: (ItemTypeable a, Monad m) => a -> Range -> m [Annoted Item] ->
           m Item
mkItemM it rg l = l >>= return . mkItem it rg

mkItemMM :: (ItemTypeable a, Monad m) => a -> Range -> [m (Annoted Item)] ->
            m Item
mkItemMM it rg = mkItemM it rg . sequence

mkFlatItemM :: (ItemTypeable a, Monad m) => a -> Range -> m Item
mkFlatItemM it rg = return $ mkFlatItem it rg

flattenItem :: Item -> Item
flattenItem x = x { isFlat = True }

addRange :: Range -> Item -> Item
addRange rg x = x { range = rg }
