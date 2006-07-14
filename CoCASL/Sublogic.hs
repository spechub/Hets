{- |

Module      :  $Header$
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  experimental
Portability :  portable

This module provides the sublogic functions (as required by Logic.hs)
  for CoCASL. It is based on the respective functions for CASL.

Todo: extend this to the coalgebraic features.

-}

module CoCASL.Sublogic where


import Data.Maybe
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.AS_Annotation
import CASL.Sublogic
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism

------------------------------------------------------------------------------
-- | Datatypes for CoCASL sublogics
------------------------------------------------------------------------------

type CoCASL_Sublogics = CASL_SL Bool

has_co :: CoCASL_Sublogics -> Bool
has_co = ext_features
