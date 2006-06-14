{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  experimental
Portability :  portable 

latex output of the abstract syntax
-}

module COL.LaTeX_COL where

import COL.AS_COL
import COL.COLSign
import COL.Print_AS()
import Common.PrettyPrint
import Common.DocUtils

instance PrintLaTeX COL_SIG_ITEM where 
    printLatex0 = toOldLatex

instance PrintLaTeX COLSign where 
    printLatex0 = toOldLatex
