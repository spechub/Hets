{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
   latex output of the abstract syntax
-}

module Modal.LaTeX_Modal where

import Modal.AS_Modal
import Modal.ModalSign
import Common.PrettyPrint

instance PrintLaTeX M_FORMULA where 
    printLatex0 = printText0

instance PrintLaTeX M_SIG_ITEM where 
    printLatex0 = printText0

instance PrintLaTeX M_BASIC_ITEM where 
    printLatex0 = printText0

instance PrintLaTeX ModalSign where 
    printLatex0 = printText0
