{- |
Module      :  $Header$
Description :  Meta information about Maude data types
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

module Maude.Meta (
    module HasName,
    module HasSorts,
    module HasOps,
    module HasLabels,
    module AsSymbol,
) where


import Maude.Meta.HasName as HasName
import Maude.Meta.HasSorts as HasSorts
import Maude.Meta.HasOps as HasOps
import Maude.Meta.HasLabels as HasLabels
import Maude.Meta.AsSymbol as AsSymbol
