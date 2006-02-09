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
import Common.Keywords
import Common.PrettyPrint -- todo provide real latex printers
import Common.Lib.Pretty
import Common.PrintLaTeX
import Common.LaTeX_utils
import Common.PPUtils
import Common.AS_Annotation
import Common.LaTeX_AS_Annotation
import CASL.AS_Basic_CASL
import CASL.LaTeX_AS_Basic

instance PrintLaTeX C_FORMULA where
    printLatex0 = printText0

instance PrintLaTeX C_SIG_ITEM where
    printLatex0 ga (CoDatatype_items l _) =
        hc_sty_sig_item_keyword ga (cotypeS++pluralS l) <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)

instance PrintLaTeX CODATATYPE_DECL where
    printLatex0 ga (CoDatatype_decl s a _) =
        printLatex0 ga s <\+> barT_latex ga a

instance PrintLaTeX COALTERNATIVE where
    printLatex0 ga (Co_construct k n l _) = tabbed_nest_latex (
        printLatex0 ga n <> (if null l then case k of
                             Partial -> parens_tab_latex empty
                             _ -> empty
                            else parens_tab_latex $ semiT_latex ga l)
                            <> optLatexQuMark k)
    printLatex0 ga (CoSubsorts l _) =
        hc_sty_id (sortS ++ pluralS l) <\+> commaT_latex ga l

instance PrintLaTeX COCOMPONENTS where
    printLatex0 ga (CoSelect l s _) =
        commaT_latex ga l <> colon_latex <> printLatex0 ga s

instance PrintLaTeX C_BASIC_ITEM where
    printLatex0 ga (CoFree_datatype l _) =
        fsep_latex [hc_sty_plain_keyword cofreeS
                    <~> setTab_latex
                    <> hc_sty_plain_keyword (typeS ++ pluralS l)
                   ,tabbed_nest_latex $ semiAnno_latex ga l]
    printLatex0 ga (CoSort_gen l _) = case l of
        [Annoted (Ext_SIG_ITEMS (CoDatatype_items l' _)) _ lans _] ->
            hang_latex (hc_sty_plain_keyword cogeneratedS
                        <~> setTab_latex <+>
                        hc_sty_plain_keyword (cotypeS ++ pluralS l')) 9 $
                        tabbed_nest_latex (vcat (map (printLatex0 ga) lans)
                                           $$ semiAnno_latex ga l')
        _ -> hang_latex (hc_sty_plain_keyword cogeneratedS <~> setTab_latex) 9
             $ tabbed_nest_latex $ braces
                   $ vcat $ map (printLatex0 ga) l

instance PrintLaTeX CoCASLSign where
    printLatex0 = printText0
