{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

latex output of the abstract syntax
-}

module Modal.LaTeX_Modal where

import Modal.AS_Modal
import Modal.ModalSign
import Modal.Print_AS

import Common.Id
import Common.PrettyPrint (printText0)
import Common.PrintLaTeX
import Common.Lib.Pretty
import Common.Keywords
import Common.PPUtils
import Common.LaTeX_utils
import CASL.LaTeX_AS_Basic

instance PrintLaTeX M_BASIC_ITEM where
    printLatex0 ga (Simple_mod_decl is fs _) = 
        -- Warning: very bad hacking!!!
--      sp_text 0 "\\\\\n\\SPEC~\\=\\PREDS~\\=\\kill\n\\>"<>
        hc_sty_plain_keyword (pl_modalityS is) <\+> 
        tabbed_nest_latex (semiAnno_latex ga is) <\+>
        tabbed_nest_latex (braces_latex (semiAnno_latex ga fs))
    printLatex0 ga (Term_mod_decl ss fs _) = 
--      sp_text 0 "\\\\\n\\SPEC~\\=\\PREDS~\\=\\kill\n\\>"<>
        hc_sty_plain_keyword termS <\+> 
        hc_sty_plain_keyword (pl_modalityS ss) <\+> 
        tabbed_nest_latex (semiAnno_latex ga ss) <\+>
        tabbed_nest_latex (braces_latex (semiAnno_latex ga fs))

instance PrintLaTeX RIGOR where
    printLatex0 _ Rigid = hc_sty_plain_keyword rigidS
    printLatex0 _ Flexible = hc_sty_plain_keyword flexibleS

{- 
        hc_sty_sig_item_keyword ga (opS++pluralS l)   <\+> 
        set_tabbed_nest_latex (semiAnno_latex ga l) 
-}

instance PrintLaTeX M_SIG_ITEM where
    printLatex0 ga (Rigid_op_items r ls _) =
       printLatex0 ga r <\+> hc_sty_sig_item_keyword ga (opS++pluralS ls) 
        <\+> set_tabbed_nest_latex (semiAnno_latex ga ls)
    printLatex0 ga (Rigid_pred_items r ls _) =
       printLatex0 ga r <\+> hc_sty_sig_item_keyword ga (predS++pluralS ls) 
        <\+> set_tabbed_nest_latex (semiAnno_latex ga ls)

instance PrintLaTeX M_FORMULA where
    printLatex0 ga (BoxOrDiamond b t f _) =
       let t' = printLatex0 ga t
           f' = condParensInnerF (printLatex0 ga) parens_tab_latex f
           sp = case t of 
                         Simple_mod _ -> (<>)
                         _ -> (<\+>)
       in if isEmpty t' then 
          if b then hc_sty_axiom "\\Box" <> f' 
             else hc_sty_axiom "\\Diamond"  <\+> f'
          else if b then brackets_latex t' <> f'
               else hc_sty_axiom lessS `sp` t' `sp` hc_sty_axiom greaterS
                        <\+> f'

instance PrintLaTeX MODALITY where
    printLatex0 ga (Simple_mod ident) = 
        if tokStr ident == emptyS then empty
           else printLatex0 ga ident
    printLatex0 ga (Term_mod t) = printLatex0 ga t

instance PrintLaTeX ModalSign where
    printLatex0 = printText0

pl_modalityS :: [a] -> String
pl_modalityS l = if length l > 1 then modalitiesS else modalityS
