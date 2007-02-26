{- |
Module      :  $Header$
Copyright   :  (c) Andy Gimblett and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Printing abstract syntax of CSP-CASL

-}
module CspCASL.Print_CspCASL where

import CASL.ToDoc

import Common.Doc
import Common.DocUtils
import Common.Keywords (endS)

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords

instance Pretty BASIC_CSP_CASL_SPEC where
    pretty = printBasic_Csp_Casl_Spec

printBasic_Csp_Casl_Spec :: BASIC_CSP_CASL_SPEC -> Doc
printBasic_Csp_Casl_Spec (Basic_Csp_Casl_Spec d p) =
    keyword dataS <+> (pretty d) $+$
    keyword processS <+> (pretty p) $+$
    keyword endS

instance Pretty DATA_DEFN where
    pretty = printDataDefn

printDataDefn :: DATA_DEFN -> Doc
printDataDefn (Spec bs) = printBASIC_SPEC pretty pretty pretty bs 

instance Pretty PROCESS where
    pretty = printProcess

printProcess :: PROCESS -> Doc
printProcess _ = text "?"