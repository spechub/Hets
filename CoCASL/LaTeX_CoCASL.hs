{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hausmann@tzi.de
Stability   :  experimental
Portability :  portable

latex output of the abstract syntax
-}

module CoCASL.LaTeX_CoCASL where

import CoCASL.AS_CoCASL
import CoCASL.CoCASLSign
import CoCASL.Print_AS()
import Common.PrintLaTeX (PrintLaTeX(..))
import Common.DocUtils

instance PrintLaTeX C_FORMULA where
    printLatex0 = toOldLatex

instance PrintLaTeX C_SIG_ITEM where
    printLatex0 = toOldLatex

instance PrintLaTeX CODATATYPE_DECL where
    printLatex0 = toOldLatex

instance PrintLaTeX COALTERNATIVE where
    printLatex0 = toOldLatex

instance PrintLaTeX COCOMPONENTS where
    printLatex0 = toOldLatex

instance PrintLaTeX C_BASIC_ITEM where
    printLatex0 = toOldLatex
instance PrintLaTeX CoCASLSign where
    printLatex0 = toOldLatex
