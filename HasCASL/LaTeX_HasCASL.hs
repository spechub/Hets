{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
   latex output of the abstract syntax
-}

module HasCASL.LaTeX_HasCASL where

import HasCASL.As
import HasCASL.PrintAs
import HasCASL.Le
import HasCASL.Symbol
import HasCASL.PrintLe
import HasCASL.Morphism
import Common.PrettyPrint

instance PrintLaTeX BasicSpec where 
    printLatex0 = printText0

instance PrintLaTeX Env where
    printLatex0 = printText0

instance PrintLaTeX Morphism where
    printLatex0 = printText0

instance PrintLaTeX Symbol where
    printLatex0 = printText0

instance PrintLaTeX RawSymbol where
    printLatex0 = printText0

instance PrintLaTeX SymbItems where
    printLatex0 = printText0

instance PrintLaTeX SymbMapItems where
    printLatex0 = printText0



	
