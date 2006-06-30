{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

latex output of the abstract syntax
-}

module Modal.LaTeX_Modal where

import Modal.AS_Modal
import Modal.ModalSign
import Modal.Print_AS()
import Common.PrintLaTeX
import Common.Keywords
import Common.Doc
import Common.DocUtils

instance PrintLaTeX M_BASIC_ITEM where
    printLatex0 ga = toLatex ga . pretty

instance PrintLaTeX RIGOR where
    printLatex0 ga = toLatex ga . pretty

{-
        hc_sty_sig_item_keyword ga (opS++pluralS l)   <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)
-}

instance PrintLaTeX M_SIG_ITEM where
    printLatex0 ga = toLatex ga . pretty

instance PrintLaTeX M_FORMULA where
    printLatex0 ga = toLatex ga . pretty 

instance PrintLaTeX MODALITY where
    printLatex0 ga = toLatex ga . pretty 

instance PrintLaTeX ModalSign where
    printLatex0 ga = toLatex ga . pretty 

pl_modalityS :: [a] -> String
pl_modalityS l = if length l > 1 then modalitiesS else modalityS
