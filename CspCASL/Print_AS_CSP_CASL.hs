module CspCASL.Print_AS_CSP_CASL where

import CspCASL.AS_CSP_CASL
import Common.PrettyPrint
import Common.Lib.Pretty
import CASL.Print_AS_Basic

instance PrettyPrint C3PO where
    printText0 ga (Named_c3po x) = printText0 ga x
    printText0 ga (C3po x) = printText0 ga x


instance PrettyPrint NAMED_CSP_CASL_C_SPEC where
    printText0 ga (Named_csp_casl_spec sn c3spec) =
	ptext "ccspec"  <+> printText0 ga sn <+> equals $$
        nest 2 (printText0 ga c3spec) $$
        ptext "end"

instance PrettyPrint CSP_CASL_C_SPEC where
    printText0 ga (Csp_casl_c_spec dd _cd _pd) =
	ptext "data" $$
	nest 2 (printText0 ga dd)
