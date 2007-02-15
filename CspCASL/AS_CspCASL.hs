{- |

Abstract syntax of CSP-CASL (part thereof, at least).

-}

module CspCASL.AS_CspCASL where

import CASL.AS_Basic_CASL (BASIC_SPEC)
import Common.Doc
import Common.DocUtils

import CspCASL.AS_CspCASL_Process (CHANNEL_DECL,
                                   PROCESS,
                                   PROCESS_DEFN
                                  )



data BASIC_CSP_CASL_SPEC
    = Basic_Csp_Casl_Spec DATA_DEFN PROCESS
    deriving (Show)

instance Pretty BASIC_CSP_CASL_SPEC where
    pretty _ = text ""


{- First line only of:
  DATA-DEFN ::=   SPEC
                 | SPEC-DEFN
                 | LIB-IMPORT ... LIB-IMPORT SPEC
                 | LIB-IMPORT ... LIB-IMPORT SPEC-DEFN 
-}
data DATA_DEFN
    = Spec (BASIC_SPEC () () ())
    deriving (Show)




-- Hets compatability machinery, to be removed when I've completely
-- disentangled it.

data Basic_CSP_CASL_C_SPEC = Basic_csp_casl_c_spec CHANNEL_DECL PROCESS_DEFN
                                 deriving Show

instance Pretty Basic_CSP_CASL_C_SPEC where
    pretty _ = text ""


