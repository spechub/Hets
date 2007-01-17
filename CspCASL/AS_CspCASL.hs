{- |

Abstract syntax of CSP-CASL (part thereof, at least).

-}

module CspCASL.AS_CspCASL where

import CASL.AS_Basic_CASL (BASIC_SPEC)

import CspCASL.AS_CspCASL_Process (PROCESS)



data BASIC_CSP_CASL_SPEC
    = Basic_Csp_Casl_Spec DATA_DEFN PROCESS
    deriving (Show)



{- First line only of:
  DATA-DEFN ::=   SPEC
                 | SPEC-DEFN
                 | LIB-IMPORT ... LIB-IMPORT SPEC
                 | LIB-IMPORT ... LIB-IMPORT SPEC-DEFN 
-}
data DATA_DEFN
    = Spec (BASIC_SPEC () () ())
    deriving (Show)
