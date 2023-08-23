{- |
Module      :  ./Maude/Util.hs
Description :  Utility Functions
Copyright   :  (c) Martin Kuehl, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Utility functions used in the Maude language module.
-}

module Maude.Util where

import Data.Map (Map)
import qualified Data.Map as Map


{- | Apply the given Map as a function.  Works as the identity function
for items not contained in the Map. -}
mapAsFunction :: (Ord a) => Map a a -> a -> a
mapAsFunction mp name = Map.findWithDefault name name mp
