{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
module HolLight.Sublogic where

import Data.Typeable
import GHC.Generics (Generic)
import Data.Hashable

-- | sublogic

data HolLightSL = Top deriving (Show, Eq, Ord, Typeable, Generic)

instance Hashable HolLightSL
