{- |
Module      :  $Header$
Description :  Meta information about Maude data types
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Meta information about Maude data types.

Exports the classes, instances and functions from these modules:

* "Maude.Meta.HasName"

* "Maude.Meta.HasSorts"

* "Maude.Meta.HasOps"

* "Maude.Meta.HasLabels"

* "Maude.Meta.AsSymbol"
-}

module Maude.Meta
  ( module Maude.Meta.HasName
  , module Maude.Meta.HasSorts
  , module Maude.Meta.HasOps
  , module Maude.Meta.HasLabels
  , module Maude.Meta.AsSymbol
  ) where

import Maude.Meta.HasName
import Maude.Meta.HasSorts
import Maude.Meta.HasOps
import Maude.Meta.HasLabels
import Maude.Meta.AsSymbol
