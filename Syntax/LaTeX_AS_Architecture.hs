{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

LaTeX Printing the Architechture stuff of HetCASL.
-}

module Syntax.LaTeX_AS_Architecture where

import Common.Lib.Pretty
import Common.PrintLaTeX
import Common.LaTeX_utils
import Common.Keywords
import Syntax.AS_Architecture
import Syntax.LaTeX_AS_Structured()
import Syntax.Print_AS_Structured
import Syntax.Print_AS_Architecture()

instance PrintLaTeX ARCH_SPEC where
    printLatex0 ga (Basic_arch_spec aa ab _) =
        let aa' = semiT_latex ga aa
            ab' = printLatex0 ga ab
        in (hang_latex (hc_sty_plain_keyword (unitS ++ sS)) 4 aa')
                     $$ (hc_sty_plain_keyword resultS <\+> ab')
    printLatex0 ga (Arch_spec_name aa) =
        printLatex0 ga aa
    printLatex0 ga (Group_arch_spec aa _) =
        sp_braces_latex2 $ printLatex0 ga aa

instance PrintLaTeX UNIT_REF where
    printLatex0 ga (Unit_ref aa ab _) =
        let aa' = simple_id_latex aa
            ab' = printLatex0 ga ab
        in aa' <\+> hc_sty_plain_keyword toS <\+> ab'

instance PrintLaTeX UNIT_DECL_DEFN where
    printLatex0 ga (Unit_decl aa ab ac _) =
        let aa' = simple_id_latex aa
            ab' = printLatex0 ga ab
            ac' = if null ac then empty
                  else hc_sty_plain_keyword givenS <\+>
                       (commaT_latex ga ac)
        in hang_latex (aa' <> colon_latex <\+> ab') 4  ac'
    printLatex0 ga (Unit_defn aa ab _) =
        let aa' = simple_id_latex aa
            ab' = printLatex0 ga ab
        in hang_latex (aa' <\+> equals_latex) 4 ab'

instance PrintLaTeX UNIT_SPEC where
    printLatex0 ga (Unit_type aa ab _) =
        let aa' = fsep_latex $ punctuate
                  (space_latex <> hc_sty_axiom "\\times"<> space_latex)
                  $ map (condBracesGroupSpec printLatex0
                                 sp_braces_latex2 Nothing ga) aa
            ab' = condBracesGroupSpec printLatex0
                  sp_braces_latex2 Nothing ga ab
        in if null aa then ab' else
           aa' <\+> rightArrow <\+> ab'
    printLatex0 ga (Spec_name aa) =
        let aa' = printLatex0 ga aa
        in aa'
    printLatex0 ga (Closed_unit_spec aa _) =
        let aa' = printLatex0 ga aa
        in hang_latex (hc_sty_plain_keyword closedS) 4 aa'

instance PrintLaTeX REF_SPEC where
    printLatex0 ga (Unit_spec u) = printLatex0 ga u
    printLatex0 ga (Refinement b u m r _) =
       (if b then empty else
           hc_sty_plain_keyword behaviourallyS <> space_latex)
       <> hc_sty_plain_keyword refinedS <\+> printLatex0 ga u <\+>
       (if null m then empty else hc_sty_plain_keyword viaS <\+>
          commaT_latex ga m <> space_latex) <> printLatex0 ga r
    printLatex0 ga (Arch_unit_spec aa _) =
        let aa' = printLatex0 ga aa
        in hang_latex (hc_sty_plain_keyword archS
                 <\+> hc_sty_plain_keyword specS) 4 aa'
    printLatex0 ga (Compose_ref aa _) =
        listSep_latex (space_latex <> hc_sty_plain_keyword thenS) ga aa
    printLatex0 ga (Component_ref aa _) =
        sp_braces_latex2 $ commaT_latex ga aa

instance PrintLaTeX UNIT_EXPRESSION where
    printLatex0 ga (Unit_expression aa ab _) =
        let aa' = semiT_latex ga aa
            ab' = printLatex0 ga ab
        in if null aa then ab'
           else hang_latex (hc_sty_plain_keyword lambdaS) 4
                    (hang_latex aa' (-2)
                     (bullet_latex <\+> ab'))

instance PrintLaTeX UNIT_BINDING where
    printLatex0 ga (Unit_binding aa ab _) =
        let aa' = printLatex0 ga aa
            ab' = printLatex0 ga ab
        in aa' <\+> colon_latex <\+> ab'

instance PrintLaTeX UNIT_TERM where
    printLatex0 ga (Unit_reduction aa ab) =
        let aa' = printLatex0 ga aa
            ab' = printLatex0 ga ab
        in fsep_latex [aa', ab']
    printLatex0 ga (Unit_translation aa ab) =
        let aa' = printLatex0 ga aa
            ab' = printLatex0 ga ab
        in fsep [aa', ab']
    printLatex0 ga (Amalgamation aa _) =
        listSep_latex (space_latex <> hc_sty_plain_keyword andS) ga aa
    printLatex0 ga (Local_unit aa ab _) =
        let aa' = semiT_latex ga aa
            ab' = printLatex0 ga ab
        in (hang_latex (hc_sty_plain_keyword localS) 4 aa') $$
           (hang_latex (hc_sty_plain_keyword withinS) 4 ab')
    printLatex0 ga (Unit_appl aa ab _) =
        let aa' = simple_id_latex aa
            ab' = fsep_latex $ map (printLatex0 ga) ab
        in aa' <> (if null ab then empty else space_latex <> ab')
    printLatex0 ga (Group_unit_term aa _) =
        sp_braces_latex2 $ printLatex0 ga aa

instance PrintLaTeX FIT_ARG_UNIT where
    printLatex0 ga (Fit_arg_unit aa ab _) = brackets_latex $
        printLatex0 ga aa <>
        (if null ab then empty else space_latex <>
            hc_sty_plain_keyword fitS <\+>
            set_tabbed_nest_latex (fsep_latex (map (printLatex0 ga) ab)))
