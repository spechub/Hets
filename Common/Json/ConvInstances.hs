{-# LANGUAGE StandaloneDeriving, DeriveGeneric, FlexibleInstances, UndecidableInstances #-}
module Common.Json.ConvInstances where
    
import Data.Aeson
import GHC.Generics
import Common.Lib.SizedList as SizedList
import Common.Json.Instances()
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet
import qualified Common.InjMap as InjMap
import qualified Data.Relation as DRel
import qualified Data.Relation.Internal as DRelInt
import System.Time

deriving instance Generic ClockTime
deriving instance (Generic a, Generic b) => Generic (DRelInt.Relation a b)

instance ToJSON a => ToJSON (SizedList.SizedList a)
instance (Ord a, ToJSON a, Ord b, ToJSON b, ToJSONKey a, ToJSONKey b) => ToJSON (InjMap.InjMap a b) where
instance (Ord a, ToJSON a, Ord b, ToJSON b, ToJSONKey a) => ToJSON (MapSet.MapSet a b) where
instance (Ord a, ToJSON a, ToJSONKey a) => ToJSON (Rel.Rel a) where
instance (Ord a, Ord b, Generic a, Generic b, ToJSON a, ToJSON b, ToJSONKey a, ToJSONKey b) => ToJSON (DRel.Relation a b) where
instance ToJSON ClockTime where

instance FromJSON a => FromJSON (SizedList.SizedList a)
instance (Ord a, FromJSON a, Ord b, FromJSON b, FromJSONKey a, FromJSONKey b) => FromJSON (InjMap.InjMap a b) where
instance (Ord a, FromJSON a, Ord b, FromJSON b, FromJSONKey a) => FromJSON (MapSet.MapSet a b) where
instance (Ord a, FromJSON a, FromJSONKey a) => FromJSON (Rel.Rel a) where
instance (Ord a, Ord b, Generic a, Generic b, FromJSON a, FromJSON b, FromJSONKey a, FromJSONKey b) => FromJSON (DRel.Relation a b) where
instance FromJSON ClockTime where
