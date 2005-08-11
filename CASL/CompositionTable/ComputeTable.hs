{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

  Compute the composition table of a relational algebra that is
  specified in a particular way in a CASL theory.
-}

module CASL.CompositionTable.ComputeTable where

import CASL.CompositionTable.CompositionTable
import CASL.AS_Basic_CASL
import CASL.Logic_CASL

computeCompTable :: (CASLSign, [Named CASLFORMULA]) -> Table
computeCompTable = 
  error "CASL.CompositionTable.CompositionTable.computeCompTable nyi"