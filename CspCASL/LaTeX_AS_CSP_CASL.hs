{- |
Module      :  $Header$
Copyright   :  (c)  Christian Maeder and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable

latex abstract syntax of CSP-CASL

-}
module CspCASL.LaTeX_AS_CSP_CASL where

import CspCASL.AS_CSP_CASL
import CspCASL.Print_AS_CSP_CASL
import Common.Lib.Pretty
import Common.PrintLaTeX
import Common.LaTeX_utils
import CASL.LaTeX_AS_Basic

instance PrintLaTeX C3PO where
    printLatex0 ga (Named_c3po x) = printLatex0 ga x
    printLatex0 ga (C3po x) = printLatex0 ga x

instance PrintLaTeX NAMED_CSP_CASL_C_SPEC where
    printLatex0 ga (Named_csp_casl_spec sn c3spec) =
        ptext "ccspec"  <\+> printLatex0 ga sn <\+> equals $$
        nest 2 (printLatex0 ga c3spec) $$
        ptext "end"

instance PrintLaTeX CSP_CASL_C_SPEC where
    printLatex0 ga (Csp_casl_c_spec dd _cd _pd) =
        ptext "data" $$
        nest 2 (printLatex0 ga dd)

instance PrintLaTeX Basic_CSP_CASL_C_SPEC where
    printLatex0 _ga (Basic_csp_casl_c_spec _cd _pd) =
        ptext "<not printable yet>"
