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
import CASL.Sign
import Common.AS_Annotation
import Common.Id
import Common.PrettyPrint

-- Christian: I also need the name of the spec!
computeCompTable :: SIMPLE_ID -> (Sign f e, [Named (FORMULA f)]) -> Table
computeCompTable spName (sig,sens) = 
  Table attrs compTable convTable models
  where 
  attrs = Table_Attrs {tableName = showPretty spName "",
                       tableIdentity = ""}
  compTable = Compositiontable []
  convTable = Conversetable []
  models = Models []
