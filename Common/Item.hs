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

data ItemSubtype = ItemK | Decl | Defn | Free | Gen | Ext | Name | Attrib
                 | Type
                   deriving (Eq, Ord, Show)

data ItemKind = Datatype | SortK | Subsort | Var | Basic | Sig | Op | Pred
              | Iso | Term | Formula | IdK
                deriving (Eq, Ord, Show)

data NewItemType = I1 String | I2 String | I3 String

data ItemType = Abstract String String | AbstractVal String | Basicspec
              | Plur ItemType | Simple ItemKind | Localvaraxioms | Axiomitems
              | ComplexVal ItemType String | Complex ItemType String String
              | IT ItemKind ItemSubtype
              | NewIT [String]
              
                deriving (Eq, Ord, Show)

data Item = Item { itemType :: ItemType
                 , isFlat :: Bool
                 , range :: Range
--                 , attribs :: [Item]
                 , items :: [Annoted Item]
                 } deriving (Eq, Ord, Show)


showIS :: ItemSubtype -> String
showIS ItemK = "Item"
showIS is = show is

showIK :: ItemKind -> String
showIK SortK = "Sort"
showIK IdK = "Id"
showIK ik = show ik

hasValue :: ItemType -> Bool
hasValue (NewIT l) = length l > 1

hasValue (AbstractVal _) = True
hasValue (Abstract _ _) = True
hasValue (ComplexVal _ _) = True
hasValue (Complex _ _ _) = True
hasValue (Plur it) = hasValue it
hasValue _ = False

getName :: ItemType -> String
getName (NewIT (h:_)) = h

getName (Plur it) = getName it ++ "s"
getName (AbstractVal s) = s
getName (Abstract s _) = s
getName (ComplexVal it _) = getName it
getName (Complex it _ _) = getName it
getName (IT k s) =
    case s of Free -> "Free" ++ map toLower (showIK k)
              Ext  -> "Ext" ++ map toLower (showIK k)
              _ -> showIK k ++ map toLower (showIS s)
getName (Simple k) = showIK k
getName it = show it

getValue :: ItemType -> String
getValue (NewIT []) = ""
getValue (NewIT l) = last l

getValue (AbstractVal s) = s
getValue (Abstract _ s) = s
getValue (ComplexVal _ s) = s
getValue (Complex _ _ s) = s
getValue (Plur it) = getValue it
getValue _ = ""

getValueName :: ItemType -> String
getValueName (NewIT [_,v,_]) = v
getValueName (NewIT _) = "value"

getValueName (AbstractVal _) = "value"
getValueName (Abstract s _) = s
getValueName (ComplexVal _ _) = "value"
getValueName (Complex _ s _) = s
getValueName (Plur it) = getValueName it
getValueName _ = ""

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
    toIT s = NewIT [s]
instance ItemTypeable (String, String) where
    toIT (s,s') = NewIT [s,s']
instance ItemTypeable (String, String, String) where
    toIT (s,s',s'') = NewIT [s,s',s'']



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

abstract :: String -> Item
abstract s = liftIT2I $ NewIT [s]

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
