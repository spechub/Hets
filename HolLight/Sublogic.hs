{-# LANGUAGE DeriveDataTypeable #-}
module HolLight.Sublogic where

import Data.Typeable

-- | sublogic

data HolLightSL = Top deriving (Show, Eq, Ord, Typeable)
