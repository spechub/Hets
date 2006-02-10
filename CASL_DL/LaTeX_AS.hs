{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable
   
LaTeX output of the abstract syntax

-}

module CASL_DL.LaTeX_AS where

import Common.Lib.Pretty
import Common.PrintLaTeX
import Common.LaTeX_funs
import Common.LaTeX_utils

import CASL.LaTeX_AS_Basic ()
import CASL_DL.AS_CASL_DL
import CASL_DL.Print_AS ()

instance PrintLaTeX DL_FORMULA where
    printLatex0 ga (Cardinality ct pn varTerm natTerm _) = 
        hc_sty_id (case ct of
              CMin   -> minCardinalityS
              CMax   -> maxCardinalityS
              CExact -> cardinalityS)
        <> brackets_latex (printLatex0 ga pn)
        <> parens_latex (printLatex0 ga varTerm<>comma_latex<\+>
                         printLatex0 ga natTerm)
