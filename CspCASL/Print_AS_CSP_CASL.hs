module Print_AS_CSP_CASL where

import AS_CSP_CASL
import Common.PrettyPrint
import Common.Lib.Pretty
import CASL.Print_AS_Basic

instance PrettyPrint CSP_CASL_C_SPEC where
    printText0 ga (Csp_casl_c_spec dd _cd _pd) =
	ptext "data" $$
	nest 2 (printText0 ga dd)
