{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

LaTeX Printing the Architechture stuff of HetCASL.
-}

module Syntax.LaTeX_AS_Architecture() where

import Common.PrettyPrint
import Common.DocUtils
import Common.Keywords
import Syntax.AS_Architecture
import Syntax.LaTeX_AS_Structured()
import Syntax.Print_AS_Structured
import Syntax.Print_AS_Architecture()

instance PrintLaTeX ARCH_SPEC where
    printLatex0 = toOldLatex

instance PrintLaTeX UNIT_REF where
    printLatex0 = toOldLatex

instance PrintLaTeX UNIT_DECL_DEFN where
    printLatex0 = toOldLatex

instance PrintLaTeX UNIT_SPEC where
    printLatex0 = toOldLatex

instance PrintLaTeX REF_SPEC where
    printLatex0 = toOldLatex

instance PrintLaTeX UNIT_EXPRESSION where
    printLatex0 = toOldLatex

instance PrintLaTeX UNIT_BINDING where
    printLatex0 = toOldLatex

instance PrintLaTeX UNIT_TERM where
    printLatex0 = toOldLatex

instance PrintLaTeX FIT_ARG_UNIT where
    printLatex0 = toOldLatex
