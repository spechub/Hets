{- |
Module      :  $Header$
Description :  Meta information about Maude datatypes
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Meta information about Maude datatypes.
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
