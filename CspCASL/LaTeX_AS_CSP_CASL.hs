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
    printLatex0 = toLatex

instance PrintLaTeX NAMED_CSP_CASL_C_SPEC where
    printLatex0 = toLatex

instance PrintLaTeX CSP_CASL_C_SPEC where
    printLatex0 = toLatex

instance PrintLaTeX Basic_CSP_CASL_C_SPEC where
    printLatex0 = toLatex
