{- |
Module      :  $Header$
Description :  Utility Functions
Copyright   :  (c) Martin Kuehl, Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Utility functions used in the Maude language module.
-}

module Maude.Util where

import Data.Map (Map)
import qualified Data.Map as Map


mapAsFunction :: (Ord a) => Map a a -> (a -> a)
mapAsFunction mp name = Map.findWithDefault name name mp
