{- |
Module      :  $Header$
Description :  positions, simple and mixfix identifiers
Copyright   :  (c) Christian Maeder and Ewaryst Schulz and Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module provides the item datatype for an abstract logic independent
representation of basic specs.

-}

module Common.Item where

import Common.Id
import Common.AS_Annotation

data ItemType = Abstract String | Basicspec | Sortdecl | Nonempty
              | Possiblyempty | Freedatatype | Sortgen | Varitems
              | Localvaraxioms | Axiomitems | Extbasicitems | Sigitem
                deriving (Eq, Ord, Show)

data Item = Item { itemType :: ItemType
                 , range :: Range
                 , items :: [Annoted Item]
                 } deriving (Eq, Ord, Show)


rootItem :: Item
rootItem = Item Basicspec nullRange []


instance GetRange Item where
    getRange = range


-- often we have the situation where we want to obtain an ItemType
-- from a certain Type:
class ItemTypeable a where
    toIT :: a -> ItemType

-- often we have the situation where we want to obtain a whole Item
-- or even an Annoted Item from an ItemType:
liftIT2I :: ItemType -> Item
liftIT2I t = Item t nullRange []
liftIT2AI :: ItemType -> Annoted Item
liftIT2AI = emptyAnno . liftIT2I
