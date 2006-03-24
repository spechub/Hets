{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  experimental
Portability :  portable

latex printing data types of 'BASIC_SPEC'
-}

module CASL.LaTeX_AS_Basic
    ( hc_sty_sig_item_keyword
    , optLatexQuMark
    ) where

import CASL.AS_Basic_CASL
import CASL.Print_AS_Basic
import CASL.ToDoc
import qualified Common.Doc as Doc
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.LaTeX_AS_Annotation
import Common.Keywords
import Common.Lib.Pretty (Doc, empty, (<>), ($$), ($+$), fcat, vcat)
import Common.PrintLaTeX (PrintLaTeX(..))
import Common.LaTeX_utils
import Common.PPUtils (pluralS)

instance (PrintLaTeX b, PrintLaTeX s, PrintLaTeX f)
    => PrintLaTeX (BASIC_SPEC b s f) where
    printLatex0 ga (Basic_spec l) =
        if null l then sp_braces_latex2 empty
         else vcat (map (printLatex0 ga) l)

instance (PrintLaTeX b, PrintLaTeX s, PrintLaTeX f) =>
         PrintLaTeX (BASIC_ITEMS b s f) where
    printLatex0 ga (Sig_items s) = printLatex0 ga s
    printLatex0 ga (Free_datatype l _) =
        fsep_latex [hc_sty_plain_keyword freeS
                    <~> setTab_latex
                    <> hc_sty_plain_keyword (typeS ++ pluralS l)
                   ,tabbed_nest_latex $ semiAnno_latex ga l]
    printLatex0 ga (Sort_gen l _) = case l of
        [Annoted (Datatype_items l' _) _ lans _] ->
            fsep_latex [ hc_sty_plain_keyword generatedS <~> setTab_latex <\+>
                         hc_sty_plain_keyword (typeS ++ pluralS l')
                       , tabbed_nest_latex (printAnnotationList_Latex0 ga lans
                                            $$ semiAnno_latex ga l') ]
        _ -> fsep_latex [ hc_sty_plain_keyword generatedS <~> setTab_latex
                        , tabbed_nest_latex $ sp_braces_latex2
                        $ vcat $ map (printLatex0 ga) l ]
    printLatex0 ga (Var_items l _) =
        hc_sty_plain_keyword (varS ++ pluralS l) <\+>
        semiT_latex ga l
    printLatex0 ga (Local_var_axioms l f _) =
        forall_latex <\+> semiT_latex ga l
                 $$ printLatex0Axioms ga f
    printLatex0 ga (Axiom_items f _) = printLatex0Axioms ga f
    printLatex0 ga (Ext_BASIC_ITEMS b) = printLatex0 ga b

printLatex0Axioms :: PrintLaTeX f =>
               GlobalAnnos -> [Annoted (FORMULA f)] -> Doc
printLatex0Axioms ga f =
        vcat $ map (printAnnotedFormula_Latex0 ga) f

printAnnotedFormula_Latex0 :: PrintLaTeX f =>
               GlobalAnnos -> Annoted (FORMULA f) -> Doc
printAnnotedFormula_Latex0 ga (Annoted i _ las ras) =
        let i'   = bullet_latex <\+> set_tabbed_nest_latex (printLatex0 ga i)
            las' = if null las then empty
                   else space_latex $+$ printAnnotationList_Latex0 ga las
        in las' $+$ splitAndPrintRAnnos_latex ga i' ras

instance (PrintLaTeX s, PrintLaTeX f) =>
          PrintLaTeX (SIG_ITEMS s f) where
    printLatex0 ga (Sort_items l _) =
        hc_sty_sig_item_keyword ga  (sortS ++ pluralS l) <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)
    printLatex0 ga (Op_items l _) =
        hc_sty_sig_item_keyword ga (opS ++ pluralS l) <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)
    printLatex0 ga (Pred_items l _) =
        hc_sty_sig_item_keyword ga (predS ++ pluralS l) <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)
    printLatex0 ga (Datatype_items l _) =
        hc_sty_sig_item_keyword ga (typeS ++ pluralS l) <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)
    printLatex0 ga (Ext_SIG_ITEMS s) = printLatex0 ga s

instance PrintLaTeX f => PrintLaTeX (SORT_ITEM f) where
    printLatex0 ga (Sort_decl l _) = commaT_latex ga l
    printLatex0 ga (Subsort_decl l t _) =
        fsep_latex [commaT_latex ga l, less_latex, printLatex0 ga t]
    printLatex0 ga (Subsort_defn s v t f _) =
        printLatex0 ga s <\+> equals_latex <\+>
           sp_braces_latex2 (set_tabbed_nest_latex $ fsep_latex
                            [printLatex0 ga v
                             <> colon_latex
                             <\+> printLatex0 ga t,
                             bullet_latex
                             <\+> set_tabbed_nest_latex (printLatex0 ga f)])
    printLatex0 ga (Iso_decl l _) =
        listSep_latex (space_latex <> equals_latex) ga l

instance PrintLaTeX f => PrintLaTeX (OP_ITEM f) where
    printLatex0 ga (Op_decl l t a _) =
        (if na then ids_sig
        else fsep_latex [ids_sig,
                       tabbed_nest_latex $ commaT_latex ga a])
        where ids_sig = fsep_latex [commaT_latex ga l <\+> colon_latex,
                                 tabbed_nest_latex (if na then sig
                                        else sig <> comma_latex)]
              sig =  printLatex0 ga t
              na = null a
    printLatex0 ga (Op_defn n h term _) =
        fsep_latex [ printLatex0 ga n
                     <> printLatex0 ga h
                     <\+> equals_latex
                   , printLatex0 ga term]

instance PrintLaTeX OP_TYPE where
    printLatex0 = toLatex

optLatexQuMark :: FunKind -> Doc
optLatexQuMark Partial = hc_sty_axiom quMark
optLatexQuMark Total = empty

instance PrintLaTeX OP_HEAD where
    printLatex0 ga (Op_head k l s _) =
        (if null l then empty
         else parens_latex (semiT_latex ga l))
        <> colon_latex <> optLatexQuMark k
        <\+> printLatex0 ga s

instance PrintLaTeX ARG_DECL where
    printLatex0 ga (Arg_decl l s _) = commaT_latex ga l
                              <> colon_latex
                              <\+> printLatex0 ga s

instance PrintLaTeX f => PrintLaTeX (OP_ATTR f) where
    printLatex0 _ (Assoc_op_attr)   = hc_sty_id assocS
    printLatex0 _ (Comm_op_attr)    = hc_sty_id commS
    printLatex0 _ (Idem_op_attr)    = hc_sty_id idemS
    printLatex0 ga (Unit_op_attr t) = hc_sty_id unitS <\+> printLatex0 ga t

instance PrintLaTeX f => PrintLaTeX (PRED_ITEM f) where
    printLatex0 ga (Pred_decl l t _) = commaT_latex ga l
                                  <\+> colon_latex <\+> printLatex0 ga t
    printLatex0 ga (Pred_defn n h f _) =
        fsep_latex [printLatex0 ga n
                   <> printLatex0 ga h
                   <\+> hc_sty_axiom "\\Leftrightarrow",
                   printLatex0 ga f]

instance PrintLaTeX PRED_TYPE where
    printLatex0 = toLatex

instance PrintLaTeX PRED_HEAD where
    printLatex0 ga (Pred_head l _) =
        parens_latex (semiT_latex ga l)

instance PrintLaTeX DATATYPE_DECL where
    printLatex0 ga (Datatype_decl s a _) =
        printLatex0 ga s <\+> barT_latex ga a

instance PrintLaTeX ALTERNATIVE where
    printLatex0 ga (Alt_construct k n l _) = tabbed_nest_latex (
        fcat [printLatex0 ga n, (if null l then case k of
                             Partial -> parens_tab_latex empty
                             _ -> empty
                            else parens_tab_latex ( semiT_latex ga l))
                            <> optLatexQuMark k])
    printLatex0 ga (Subsorts l _) =
        hc_sty_id (sortS ++ pluralS l) <\+> commaT_latex ga l

instance PrintLaTeX COMPONENTS where
    printLatex0 ga (Cons_select k l s _) =
        commaT_latex ga l <> colon_latex <> optLatexQuMark k
                         <> printLatex0 ga s
    printLatex0 ga (Sort s) = printLatex0 ga s

instance PrintLaTeX VAR_DECL where
    printLatex0 = toLatex

instance PrintLaTeX f => PrintLaTeX (FORMULA f) where
    printLatex0 ga = Doc.toLatex ga . printFormula (fromLatex ga)

fromLatex :: PrintLaTeX a => GlobalAnnos -> a -> Doc.Doc
fromLatex ga = Doc.literalDoc . printLatex0 ga

toLatex :: Doc.Pretty a => GlobalAnnos -> a -> Doc
toLatex ga = Doc.toLatex ga . Doc.pretty

instance PrintLaTeX PRED_SYMB where
    printLatex0 = toLatex

instance PrintLaTeX f => PrintLaTeX (TERM f) where
    printLatex0 ga = Doc.toLatex ga . printTerm (fromLatex ga)

instance PrintLaTeX OP_SYMB where
    printLatex0 = toLatex

instance PrintLaTeX SYMB_ITEMS where
    printLatex0 ga (Symb_items k l _) =
        print_kind_latex k l <\+> commaT_latex ga l

instance PrintLaTeX SYMB_MAP_ITEMS where
    printLatex0 ga (Symb_map_items k l _) =
        print_kind_latex k l <\+> commaT_latex ga l

instance PrintLaTeX SYMB_KIND where
    printLatex0 _ k = print_kind_latex k [()]

instance PrintLaTeX SYMB where
    printLatex0 ga (Symb_id i) = printLatex0 ga i
    printLatex0 ga (Qual_id i t _) =
        printLatex0 ga i <\+> colon_latex <\+> printLatex0 ga t

instance PrintLaTeX TYPE where
    printLatex0 ga (O_type t) = printLatex0 ga t
    printLatex0 ga (P_type t) = printLatex0 ga t
    printLatex0 ga (A_type t) = printLatex0 ga t

instance PrintLaTeX SYMB_OR_MAP where
    printLatex0 ga (Symb s) = printLatex0 ga s
    printLatex0 ga (Symb_map s t _) =
        printLatex0 ga s <\+> mapsto_latex <\+> printLatex0 ga t

print_kind_latex :: SYMB_KIND -> [a] -> Doc
print_kind_latex k l =
    case k of
    Implicit -> empty
    _        -> hc_sty_plain_keyword $ pluralS_symb_list k l

hc_sty_sig_item_keyword :: GlobalAnnos -> String -> Doc
hc_sty_sig_item_keyword ga str =
    (if is_inside_gen_arg ga then hc_sty_plain_keyword
                             else hc_sty_casl_keyword ) str
