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
import Common.PrintLaTeX
import Common.Lib.Pretty
import Common.LaTeX_utils 

instance PrintLaTeX G_basic_spec where
    printLatex0 ga (G_basic_spec _ s) = printLatex0 ga s

instance PrintLaTeX G_sign where
    printLatex0 ga (G_sign _ s) = printLatex0 ga s

instance PrintLaTeX G_symb_items_list where
    printLatex0 ga (G_symb_items_list _ l) = 
        commaT_latex ga l

instance PrintLaTeX G_symb_map_items_list where
    printLatex0 ga (G_symb_map_items_list _ l) = 
        commaT_latex ga l
 
instance PrintLaTeX GMorphism where
    printLatex0 ga (GMorphism cid s m) = 
      ptext (show cid) 
      <+> -- ptext ":" <+> ptext (show (sourceLogic cid)) <+>
      -- ptext "->" <+> ptext (show (targetLogic cid)) <+>
      ptext "(" <+> printLatex0 ga s <+> ptext ")" 
      $$
      printLatex0 ga m
