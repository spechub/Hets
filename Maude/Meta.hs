{- |
Module      :  ./Maude/Meta.hs
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

module Maude.Meta (module X) where

import Maude.Meta.HasName as X
import Maude.Meta.HasSorts as X
import Maude.Meta.HasOps as X
import Maude.Meta.HasLabels as X
import Maude.Meta.AsSymbol as X
