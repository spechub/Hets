{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  experimental
Portability :  portable 
   
   latex output of the abstract syntax
-}

module CoCASL.LaTeX_CoCASL where

import CoCASL.AS_CoCASL
import CoCASL.CoCASLSign
import CoCASL.Print_AS
import Common.PrettyPrint

instance PrintLaTeX C_FORMULA where 
    printLatex0 = printText0

instance PrintLaTeX C_SIG_ITEM where 
    printLatex0 = printText0

instance PrintLaTeX C_BASIC_ITEM where 
    printLatex0 = printText0

instance PrintLaTeX CoCASLSign where 
    printLatex0 = printText0
