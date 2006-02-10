{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

LaTeX Printing the Structured part of heterogenous specifications.
-}

module Syntax.LaTeX_AS_Structured() where

import Common.Lib.Pretty (Doc, empty, (<>), ($$), punctuate)
import Common.PrintLaTeX (PrintLaTeX(..))
import Common.LaTeX_utils
import Common.LaTeX_AS_Annotation()
import Common.Keywords

import Syntax.AS_Structured
import Syntax.Print_AS_Structured
import Common.AS_Annotation
import Common.GlobalAnnotations
import Logic.LaTeX_Grothendieck()

instance PrintLaTeX SPEC where
    printLatex0 ga (Basic_spec aa) =
        tabbed_nest_latex $ printLatex0 ga aa
    printLatex0 ga (Translation aa ab) =
        let aa' = condBracesTransReduct printLatex0
                           sp_braces_latex2 ga aa
            ab' = printLatex0 ga ab
        in tab_hang_latex aa' 8 ab'
    printLatex0 ga (Reduction aa ab) =
        let aa' = condBracesTransReduct printLatex0
                        sp_braces_latex2 ga aa
            ab' = printLatex0 ga ab
        in tab_hang_latex aa' 8 ab'
    printLatex0 ga (Union aa _) = fsep_latex $ intersperse' aa
        where intersperse' [] = []
              intersperse' (x:xs) =
                  (condBracesAnd printLatex0 sp_braces_latex2 ga x):
                  map (\y -> hc_sty_plain_keyword andS $$
                       condBracesAnd printLatex0 sp_braces_latex2 ga y)
                      xs
    printLatex0 ga (Extension aa _) =
        fsep_latex $ printList aa
        where printList [] = []
              printList (x:xs) =
                  (sp_space <> printLatex0 ga' x):
                    map (spAnnotedPrint (printLatex0 ga')
                         (printLatex0 ga') (<\+>)
                                (hc_sty_hetcasl_keyword thenS)) xs
              (sp_space,ga') = sp_space_latex ga
    printLatex0 ga (Free_spec aa _) =
        tabbed_nest_latex (condBracesGroupSpec printLatex0
                                          sp_braces_latex2 mkw ga aa)
        where mkw =
                  mkMaybeKeywordTuple $ hc_sty_plain_keyword freeS
    printLatex0 ga (Cofree_spec aa _) =
        tabbed_nest_latex (condBracesGroupSpec printLatex0
                                          sp_braces_latex2 mkw ga aa)
        where mkw =
                  mkMaybeKeywordTuple $ hc_sty_plain_keyword cofreeS
    printLatex0 ga (Local_spec aa ab _) =
        let aa' = sp_braces_latex2 $ set_tabbed_nest_latex $
                  (cond_space<> printLatex0 ga aa)
            ab' = condBracesWithin printLatex0 sp_braces_latex2 ga ab
            cond_space = case skip_Group $ item aa of
                         Extension _ _ -> spacetab
                         Union _ _ -> spacetab
                         _ -> empty
            spacetab = view_hspace <> setTab_latex
        in tabbed_nest_latex (setTabWithSpaces_latex 3 <>
                 fsep_latex [hc_sty_plain_keyword localS,
                             tabbed_nest_latex aa',
                             hc_sty_plain_keyword withinS,
                             tabbed_nest_latex ab'])
    printLatex0 ga (Closed_spec aa _) =
        tabbed_nest_latex (condBracesGroupSpec printLatex0
                                           sp_braces_latex2 mkw ga aa)
        where mkw = mkMaybeKeywordTuple $ hc_sty_plain_keyword closedS
    printLatex0 ga (Group aa _) =
        printLatex0 ga aa
    printLatex0 ga (Spec_inst aa ab _) =
        let aa' = simple_id_latex aa
            ga' = set_inside_gen_arg True (set_first_spec_in_param True ga)
        in tabbed_nest_latex $
           if null ab
           then aa'
           else aa' <\+> set_tabbed_nest_latex
                    (fsep_latex $
                      map (brackets_latex.
                           (\x -> set_tabbed_nest_latex
                                  (printLatex0 ga' x))) ab)
    printLatex0 ga (Qualified_spec ln asp _) =
        latexLogicEnc ga ln <> colon_latex $$ printLatex0 ga asp
    printLatex0 ga (Data _ _ s1 s2 _) =
        hc_sty_plain_keyword dataS <\+> (printLatex0 ga s1)
                                 $$ (printLatex0 ga s2)

latexLogicEnc :: PrintLaTeX a => GlobalAnnos -> a -> Doc
latexLogicEnc ga a = hc_sty_plain_keyword logicS <\+> printLatex0 ga a

instance PrintLaTeX RENAMING where
    printLatex0 ga (Renaming aa _) =
       hc_sty_plain_keyword withS <\+>
          set_tabbed_nest_latex (commaT_latex ga aa)

instance PrintLaTeX RESTRICTION where
    printLatex0 ga (Hidden aa _) =
       hc_sty_plain_keyword hideS <\+>
          set_tabbed_nest_latex (commaT_latex ga aa)
    printLatex0 ga (Revealed aa _) =
        hc_sty_plain_keyword revealS <\+>
          set_tabbed_nest_latex (printLatex0 ga aa)

{- Is declared in Print_AS_Library
instance PrettyPrint SPEC_DEFN where
-}

instance PrintLaTeX G_mapping where
    printLatex0 ga (G_symb_map gsmil) = printLatex0 ga gsmil
    printLatex0 ga (G_logic_translation enc) = latexLogicEnc ga enc

instance PrintLaTeX G_hiding where
    printLatex0 ga (G_symb_list gsil) = printLatex0 ga gsil
    printLatex0 ga (G_logic_projection enc) = latexLogicEnc ga enc

instance PrintLaTeX GENERICITY where
    printLatex0 ga (Genericity aa@(Params al) ab@(Imported bl) _) =
        let aa' = set_tabbed_nest_latex $ printLatex0 ga aa
            ab' = printLatex0 ga ab
        in if null al
              then ab'
              else if null bl
                   then aa'
                   else fsep_latex [aa'<~>setTab_latex,
                                    tabbed_nest_latex $ ab']

instance PrintLaTeX PARAMS where
    printLatex0 ga (Params aa) =
        if null aa then empty
        else sep_latex $
                      map (brackets_latex.
                           (\x -> set_tabbed_nest_latex
                                  (printLatex0 ga' x))) aa
        where ga' = set_inside_gen_arg True (set_first_spec_in_param True ga)

instance PrintLaTeX IMPORTED where
    printLatex0 ga (Imported aa) =
        let mkw = mkMaybeKeywordTuple $ hc_sty_plain_keyword givenS
            coBrGrSp = condBracesGroupSpec printLatex0 sp_braces_latex2
            taa = tail aa
            taa' = if null taa then []
                   else punctuate comma_latex $ tabList_latex $
                           map ( coBrGrSp Nothing ga) taa
            condComma = if null taa then empty else comma_latex
        in if null aa then empty
           else  fsep_latex ((coBrGrSp mkw ga (head aa) <> condComma): taa')

instance PrintLaTeX FIT_ARG where
    printLatex0 ga (Fit_spec aa ab _) =
        let aa' = printLatex0 ga aa
            ab' = fsep_latex $ map (printLatex0 ga) ab
        in if null ab then aa'
        else fsep_latex [aa',
                             hc_sty_plain_keyword fitS <\+>
                                 set_tabbed_nest_latex ab']
    printLatex0 ga (Fit_view aa ab _) =
        let aa' = simple_id_latex aa
            ab' = print_fit_arg_list printLatex0
                                     brackets_latex
                                     sep_latex
                                     ga ab
            view_name = hc_sty_plain_keyword viewS <\+> aa'
        in if null ab then view_name else
           setTabWithSpaces_latex 16 <> tab_hang_latex view_name 16 ab'

{- This can be found in Print_AS_Library
instance PrintLaTeX VIEW_DEFN where
-}

instance PrintLaTeX Logic_code where
    printLatex0 ga (Logic_code (Just enc) (Just src) (Just tar) _) =
        printLatex0 ga enc <\+> colon_latex <\+>
        printLatex0 ga src <\+> rightArrow <\+>
        printLatex0 ga tar
    printLatex0 ga (Logic_code (Just enc) (Just src) Nothing _) =
        printLatex0 ga enc <\+> colon_latex <\+>
        printLatex0 ga src <\+> rightArrow
    printLatex0 ga (Logic_code (Just enc) Nothing (Just tar) _) =
        printLatex0 ga enc <\+> colon_latex <\+>
        rightArrow <\+> printLatex0 ga tar
    printLatex0 ga (Logic_code Nothing (Just src) (Just tar) _) =
        printLatex0 ga src <\+> rightArrow <\+>
        printLatex0 ga tar
    printLatex0 ga (Logic_code (Just enc) Nothing Nothing _) =
        printLatex0 ga enc
    printLatex0 ga (Logic_code Nothing (Just src) Nothing _) =
        printLatex0 ga src <\+> rightArrow
    printLatex0 ga (Logic_code Nothing Nothing (Just tar) _) =
        rightArrow <\+> printLatex0 ga tar
    printLatex0 _ (Logic_code Nothing Nothing Nothing _) =
        error "PrintLaTeX Logic_code"

instance PrintLaTeX Logic_name where
    printLatex0 ga (Logic_name mlog slog) =
        printLatex0 ga mlog <>
                       (case slog of
                       Nothing -> empty
                       Just sub -> dot_latex <> printLatex0 ga sub)

mkMaybeKeywordTuple :: Doc -> Maybe (String,Doc)
mkMaybeKeywordTuple kw_doc =
    Just (show $ kw_doc<~>setTab_latex, kw_doc <> space_latex)

sp_space_latex :: GlobalAnnos -> (Doc, GlobalAnnos)
sp_space_latex ga = if is_inside_gen_arg ga && is_first_spec_in_param ga
                    then (view_hspace, set_first_spec_in_param False ga)
                    else (empty, ga)
