module CASL_DL.CASL_DL2CASLHelpers where

import Common.Id
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import CASL.Sign
import Data.Set as Set
import Data.Map as Map
import Common.Lib.Rel as Rel

predCardResSig = inlineSign CASL
                "sorts gn_Nat, Object, gn_Pos, gn_Subject \n"

predCardResAx = inlineVars CASL
                "sorts gn_Nat, Object, gn_Pos, gn_Subject \n"
