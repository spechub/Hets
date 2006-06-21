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

import Common.PrettyPrint
import Common.DocUtils
import CASL_DL.AS_CASL_DL
import CASL_DL.Print_AS ()

instance PrintLaTeX DL_FORMULA where
   printLatex0 = toOldLatex
