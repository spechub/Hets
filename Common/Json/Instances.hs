{-# LANGUAGE StandaloneDeriving, DeriveGeneric, FlexibleInstances, UndecidableInstances #-}
module Common.Json.Instances () where

import GHC.Generics
import Data.Aeson

instance {-# OVERLAPS #-} (Generic a, GToJSON Zero (Rep a)) => ToJSON a where
instance {-# OVERLAPS #-} (Generic a, GFromJSON Zero (Rep a)) => FromJSON a where

instance {-# OVERLAPS #-} (Generic a, ToJSON a) => ToJSONKey a where
instance {-# OVERLAPS #-} (Generic a, FromJSON a) => FromJSONKey a where