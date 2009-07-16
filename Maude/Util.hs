module Maude.Util where

import Data.Map (Map)
import qualified Data.Map as Map


mapAsFunction :: (Ord a) => Map a a -> (a -> a)
mapAsFunction mp name = Map.findWithDefault name name mp
