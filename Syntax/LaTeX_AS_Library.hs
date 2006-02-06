{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

LaTeX Pretty Printing heterogenous
   libraries in HetCASL.
-}

module Syntax.LaTeX_AS_Library where

import Common.Lib.Pretty
import Common.PrintLaTeX
import Common.LaTeX_utils
import Common.GlobalAnnotations
import Common.Keywords

import Common.Id
import qualified Syntax.AS_Structured as AS_Struct
import Syntax.AS_Library

import Syntax.LaTeX_AS_Architecture()
import Syntax.LaTeX_AS_Structured()
import Syntax.Print_AS_Structured
import Syntax.Print_AS_Library

instance PrintLaTeX LIB_DEFN where
    printLatex0 ga (Lib_defn aa ab _ ad) =
        let aa' = printLatex0 ga' aa              -- lib name
            ab' = vcat $ map (printLatex0 ga') ab -- LIB_ITEMs
            ad' = vcat $ map (printLatex0 ga') ad -- global ANNOTATIONs
            ga' = set_latex_print True ga
        in hc_sty_plain_keyword libraryS <\+> aa'
               <> lnl $$ ad'
               $$ lnl $$ ab'

instance PrintLaTeX LIB_ITEM where
    printLatex0 ga (Spec_defn aa ab ac _) =
        let aa' = simple_id_indexed_latex aa
            ab' = printLatex0 ga ab -- only PARAMS are nested/hang after
                                    -- the spec name
            spec_head = hc_sty_hetcasl_keyword specS
                        <\+> setTab_latex <> aa' <\+> ab' <\+> equals_latex
            ac' = spAnnotedPrint (printLatex0 ga)
                  (printLatex0 ga) (<\+>) (spec_head) ac
        in ac' $$ latexEnd
    printLatex0 ga (View_defn aa ab ac ad _) =
        let aa' = simple_id_latex aa
            ab' = case printLatex0 ga ab of
                  ab_d
                      | isEmpty ab_d -> empty
                      | otherwise    -> ab_d
            condGrpSp = condBracesGroupSpec4View_defn
                             printLatex0
                             sp_braces_latex2 ga
            (frm,to) = case ac of
                       AS_Struct.View_type vaa vab _ ->
                            (condGrpSp vaa,
                             condGrpSp vab)
            ad' = fcat $ punctuate (comma_latex<>space_latex) $
                         map (printLatex0 ga) ad
            eq' = if null ad then empty else equals_latex
            vhead = hc_sty_hetcasl_keyword viewS <\+>
                   setTab_latex <> aa' <\+> ab'
            to' = if isEmpty eq' then to else to <\+> eq'
            head_with_type =
                fsep [vhead <\+> colon_latex,
                      fsep [frm <\+> hc_sty_plain_keyword toS,
                      to']]
            in (if isEmpty eq'
                then head_with_type
                else head_with_type $$ tabbed_nest_latex ad'
               )
                   $$ latexEnd
    printLatex0 ga (Arch_spec_defn aa ab _) =
        let aa' = simple_id_latex aa
            ab' = printLatex0 ga ab
        in (hang_latex
                (hc_sty_plain_keyword archS <\+>
                 hc_sty_plain_keyword specS <\+> aa'
                 <\+> equals_latex)
                4 ab')
           $$ latexEnd
    printLatex0 ga (Unit_spec_defn aa ab _) =
        let aa' = hc_sty_id $ tokStr aa
            ab' = printLatex0 ga ab
        in (hang_latex (hc_sty_plain_keyword unitS <\+>
                        hc_sty_plain_keyword specS <\+> aa'
                        <\+> equals_latex)
                       4 ab')
           $$ latexEnd
    printLatex0 ga (Ref_spec_defn aa ab _) =
        let aa' = hc_sty_id $ tokStr aa
            ab' = printLatex0 ga ab
        in (hang_latex (hc_sty_plain_keyword refinementS <\+> aa'
                        <\+> equals_latex)
                       4 ab')
           $$ latexEnd
    printLatex0 ga (Download_items aa ab _) =
        let aa' = printLatex0 ga aa
            ab' = fsep_latex $ punctuate comma_latex $
                               map (printLatex0 ga) ab
        in (hang_latex (hc_sty_hetcasl_keyword fromS <\+> setTab_latex <>aa'
                        <\+> hc_sty_plain_keyword getS)
                       8
                       (tabbed_nest_latex ab')) <> lnl
    printLatex0 ga (Syntax.AS_Library.Logic_decl aa _) =
        let aa' = printLatex0 ga aa
        in hc_sty_plain_keyword logicS <\+> aa'

instance PrintLaTeX ITEM_NAME_OR_MAP where
    printLatex0 _ga (Item_name aa) =
        simple_id_latex aa
    printLatex0 _ga (Item_name_map aa ab _) =
        simple_id_latex aa <\+> hc_sty_axiom "\\mapsto" <\+> simple_id_latex ab

instance PrintLaTeX LIB_NAME where
    printLatex0 ga (Lib_version aa ab) =
        let aa' = printLatex0 ga aa
            ab' = printLatex0 ga ab
        in aa' <\+> hc_sty_plain_keyword versionS <\+> ab'
    printLatex0 ga (Lib_id aa) = printLatex0 ga aa

instance PrintLaTeX LIB_ID where
    printLatex0 _ (Direct_link aa _) =
        hc_sty_structid aa
    printLatex0 _ (Indirect_link aa _) =
        hc_sty_structid aa

instance PrintLaTeX VERSION_NUMBER where
    printLatex0 _ (Version_number aa _) =
        hcat $ punctuate (casl_normal_latex ".") $ map casl_normal_latex aa

lnl :: Doc
lnl = latex_macro "\n"

latexEnd :: Doc
latexEnd = hc_sty_plain_keyword endS <> lnl
