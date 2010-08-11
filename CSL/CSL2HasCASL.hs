{- |
Module      :  $Header$
Description :  Helper functions for Prop2CASL
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  GPLv2 or higher

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable (imports Logic.Logic)

The helpers for translating comorphism from Propositional to CASL.

-}

module CSL.CSL2HasCASL
    where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import qualified Common.Result as Result

-- CSL
import qualified CSL.AS_BASIC_CSL as RBasic
-- import qualified CSL.Sublogic as PSL
import qualified CSL.Sign as RSign
import qualified CSL.Morphism as RMor
import qualified CSL.Symbol as PSymbol

-- HasCASL
import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.Sublogic as HasSub
import HasCASL.FoldTerm as HasFold

