{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

LaTeX Printing the Structured part of heterogenous specifications.
-}

module Syntax.LaTeX_AS_Structured() where

import Common.PrintLaTeX (PrintLaTeX(..))
import Common.LaTeX_AS_Annotation()
import Common.DocUtils

import Syntax.AS_Structured
import Syntax.Print_AS_Structured()
import Logic.LaTeX_Grothendieck()

instance PrintLaTeX SPEC where
    printLatex0 = toOldLatex

instance PrintLaTeX RENAMING where
    printLatex0 = toOldLatex

instance PrintLaTeX RESTRICTION where
    printLatex0 = toOldLatex
{- Is declared in Print_AS_Library
instance PrettyPrint SPEC_DEFN where
-}

instance PrintLaTeX G_mapping where
    printLatex0 = toOldLatex

instance PrintLaTeX G_hiding where
    printLatex0 = toOldLatex

instance PrintLaTeX GENERICITY where
    printLatex0 = toOldLatex

instance PrintLaTeX PARAMS where
    printLatex0 = toOldLatex

instance PrintLaTeX IMPORTED where
    printLatex0 = toOldLatex

instance PrintLaTeX FIT_ARG where
    printLatex0 = toOldLatex

{- This can be found in Print_AS_Library
instance PrintLaTeX VIEW_DEFN where
-}

instance PrintLaTeX Logic_code where
    printLatex0 = toOldLatex

instance PrintLaTeX Logic_name where
    printLatex0 = toOldLatex
