{- |
Module      :  $Header$
Description :  Meta representation of Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Meta representation of Maude.
-}
{-
  Ref.

  ...
-}

module Maude.Meta (
    module Qid,
    module Term,
    module Module,
    module HasSorts,
    module HasOps,
    module HasLabels,
) where


import Maude.Meta.Qid as Qid
import Maude.Meta.Term as Term
import Maude.Meta.Module as Module
import Maude.Meta.HasSorts as HasSorts
import Maude.Meta.HasOps as HasOps
import Maude.Meta.HasLabels as HasLabels
