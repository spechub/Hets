{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
latex output of the abstract syntax
-}

module CASL_DL.LaTeX_AS where

import CASL_DL.AS_CASL_DL
-- import CASL_DL.Sign
import CASL_DL.Print_AS

import Common.PrettyPrint (printText0)
import Common.PrintLaTeX

instance PrintLaTeX DL_FORMULA where
    printLatex0 = printText0