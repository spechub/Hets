{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, and Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Grothendieck)

latex printing
-}

module Logic.LaTeX_Grothendieck where

import Logic.Grothendieck
import Common.PrettyPrint
import Common.DocUtils

instance PrintLaTeX G_basic_spec where
    printLatex0 = toOldLatex

instance PrintLaTeX G_sign where
    printLatex0 = toOldLatex

instance PrintLaTeX G_symb_items_list where
    printLatex0 = toOldLatex

instance PrintLaTeX G_symb_map_items_list where
    printLatex0 = toOldLatex

instance PrintLaTeX GMorphism where
    printLatex0 = toOldLatex
