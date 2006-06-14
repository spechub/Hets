{- |
Module      :  $Header$
Copyright   :  (c)  Daniel Pratsch and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable

printing abstract syntax of CSP-CASL

-}
module CspCASL.Print_AS_CSP_CASL where

import CspCASL.AS_CSP_CASL
import Common.PrettyPrint
import Common.Doc
import Common.DocUtils
import CASL.ToDoc

instance PrettyPrint C3PO where
    printText0 = toOldText

instance Pretty C3PO where
    pretty c3p = case c3p of
      Named_c3po x -> printNAMED_CSP_CASL_C_SPEC x
      C3po x -> printCSP_CASL_C_SPEC x

instance PrettyPrint NAMED_CSP_CASL_C_SPEC where
    printText0 = toOldText

instance Pretty NAMED_CSP_CASL_C_SPEC where
    pretty = printNAMED_CSP_CASL_C_SPEC

printNAMED_CSP_CASL_C_SPEC :: NAMED_CSP_CASL_C_SPEC -> Doc
printNAMED_CSP_CASL_C_SPEC (Named_csp_casl_spec sn c3spec) =
    text "ccspec"  <+> sidDoc sn <+> equals $+$
    printCSP_CASL_C_SPEC c3spec $+$
    text "end"

instance PrettyPrint CSP_CASL_C_SPEC where
    printText0 = toOldText

instance Pretty CSP_CASL_C_SPEC where
    pretty = printCSP_CASL_C_SPEC

printCSP_CASL_C_SPEC :: CSP_CASL_C_SPEC -> Doc
printCSP_CASL_C_SPEC (Csp_casl_c_spec dd _cd _pd) =
    text "data" $+$
    printBASIC_SPEC pretty pretty pretty dd

instance PrettyPrint Basic_CSP_CASL_C_SPEC where
    printText0 = toOldText

instance Pretty Basic_CSP_CASL_C_SPEC where
    pretty = printBasic_CSP_CASL_C_SPEC

printBasic_CSP_CASL_C_SPEC :: Basic_CSP_CASL_C_SPEC -> Doc
printBasic_CSP_CASL_C_SPEC (Basic_csp_casl_c_spec _cd _pd) =
    text "<not printable yet>"
