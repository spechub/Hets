{- |
Module      :  $Header$
Copyright   :  (c) Andy Gimblett and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Printing abstract syntax of CSP-CASL

-}
module Print_CspCASL where

import Common.Doc
import Common.DocUtils

import AS_CspCASL

instance Pretty BASIC_CSP_CASL_SPEC where
    pretty = printBasic_Csp_Casl_Spec

printBasic_Csp_Casl_Spec :: BASIC_CSP_CASL_SPEC -> Doc
printBasic_Csp_Casl_Spec (Basic_Csp_Casl_Spec _ _) =
    text "<not yet implemented>"
