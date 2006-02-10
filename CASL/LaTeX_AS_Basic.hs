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
import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.LaTeX_AS_Annotation
import Common.Keywords
import Common.Lib.Pretty (Doc, empty, (<>), ($$), ($+$), vcat, punctuate)
import Common.PrintLaTeX (PrintLaTeX(..), printDisplayToken_latex)
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
            hang_latex (hc_sty_plain_keyword generatedS
                        <~> setTab_latex <\+>
                        hc_sty_plain_keyword (typeS ++ pluralS l')) 9 $
                        tabbed_nest_latex (printAnnotationList_Latex0 ga lans
                                           $$ semiAnno_latex ga l')
        _ -> hang_latex (hc_sty_plain_keyword generatedS <~> setTab_latex) 9 $
               tabbed_nest_latex $ sp_braces_latex2
                   $ vcat $ map (printLatex0 ga) l
    printLatex0 ga (Var_items l _) =
        hc_sty_plain_keyword (varS ++ pluralS l) <\+>
        semiT_latex ga l
    printLatex0 ga (Local_var_axioms l f _) =
        forall_latex <\+> semiT_latex ga l
                 $$ printLatex0Axioms ga f
    printLatex0 ga (Axiom_items f _) =
        printLatex0Axioms ga f
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
        hc_sty_sig_item_keyword ga (opS ++ pluralS l)   <\+>
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
        hang_latex (commaT_latex ga l) 8 $
                   less_latex <\+> printLatex0 ga t
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
        setTabWithSpaces_latex 4 <>
        (if na then ids_sig
        else fsep_latex [ids_sig,
                       tabbed_nest_latex $ commaT_latex ga a])
        where ids_sig = fsep_latex [commaT_latex ga l <\+> colon_latex,
                                 tabbed_nest_latex (if na then sig
                                        else sig <> comma_latex)]
              sig =  printLatex0 ga t
              na = null a

    printLatex0 ga (Op_defn n h term _) =
        setTabWithSpaces_latex 4 <>
        tab_hang_latex (printLatex0 ga n
                        <> printLatex0 ga h
                        <\+> equals_latex)
                 4 (printLatex0 ga term)

instance PrintLaTeX OP_TYPE where
    printLatex0 ga (Op_type Total l s _) =
        let (arg_types,type_arr) = if null l then (empty,empty)
                                   else (space_latex <>
                                         crossT_latex ga l,
                                         rightArrow)
            result_type = printLatex0 ga s
        in if null l then result_type
           else sep_latex [arg_types,type_arr <\+> result_type]

    printLatex0 ga (Op_type Partial l s _) =
        (if null l then hc_sty_axiom quMark
         else space_latex
              <> crossT_latex ga l
               <\+> pfun_latex)
        <\+> printLatex0 ga s

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
        sep_latex [printLatex0 ga n
                   <> printLatex0 ga h
                   <\+> hc_sty_axiom "\\Leftrightarrow",
                   printLatex0 ga f]

instance PrintLaTeX PRED_TYPE where
    printLatex0 _ (Pred_type [] _) = parens_latex empty
    printLatex0 ga (Pred_type l _) = crossT_latex ga l

instance PrintLaTeX PRED_HEAD where
    printLatex0 ga (Pred_head l _) =
        parens_latex (semiT_latex ga l)

instance PrintLaTeX DATATYPE_DECL where
    printLatex0 ga (Datatype_decl s a _) =
        printLatex0 ga s <\+> barT_latex ga a

instance PrintLaTeX ALTERNATIVE where
    printLatex0 ga (Alt_construct k n l _) = tabbed_nest_latex (
        printLatex0 ga n <> (if null l then case k of
                             Partial -> parens_tab_latex empty
                             _ -> empty
                            else parens_tab_latex ( semiT_latex ga l))
                            <> optLatexQuMark k)
    printLatex0 ga (Subsorts l _) =
        hc_sty_id (sortS ++ pluralS l) <\+> commaT_latex ga l

instance PrintLaTeX COMPONENTS where
    printLatex0 ga (Cons_select k l s _) =
        commaT_latex ga l <> colon_latex <> optLatexQuMark k
                         <> printLatex0 ga s
    printLatex0 ga (Sort s) = printLatex0 ga s

instance PrintLaTeX VAR_DECL where
    printLatex0 ga (Var_decl l s _) = commaT_latex ga l
                                <> colon_latex
                                <\+> printLatex0 ga s

instance PrintLaTeX f => PrintLaTeX (FORMULA f) where
    printLatex0 ga (Quantification q l f _) =
       set_tabbed_nest_latex $ fsep_latex
           [printLatex0 ga q <\+> semiT_latex ga l ,
             bullet_latex
                <\+> set_tabbed_nest_latex (printLatex0 ga f)]
    printLatex0 ga (Conjunction fs _) =
        sep_latex $ punctuate (space_latex <> hc_sty_axiom "\\wedge")
          $ map (condParensXjunction printLatex0 parens_tab_latex ga) fs
    printLatex0 ga (Disjunction  fs _) =
        sep_latex $ punctuate (space_latex <> hc_sty_axiom "\\vee")
          $ map (condParensXjunction printLatex0 parens_tab_latex ga) fs
    printLatex0 ga i@(Implication f g b _) =
        if not b
        then (
        hang_latex (condParensImplEquiv printLatex0 parens_tab_latex
                    ga i g False <\+> hc_sty_id ifS) 3 $
             condParensImplEquiv printLatex0 parens_tab_latex ga i f True)

        else (
        hang_latex (condParensImplEquiv printLatex0 parens_tab_latex
                    ga i f False <\+> hc_sty_axiom "\\Rightarrow") 3 $
             condParensImplEquiv printLatex0 parens_tab_latex ga i g True)
    printLatex0 ga e@(Equivalence  f g _) =
        sep_latex
             [condParensImplEquiv printLatex0 parens_tab_latex ga e f False
                    <\+> hc_sty_axiom "\\Leftrightarrow",
              condParensImplEquiv printLatex0 parens_tab_latex ga e g True]
    printLatex0 ga (Negation f _) = hc_sty_axiom "\\neg" <\+>
        condParensNeg f parens_latex (printLatex0 ga f)
    printLatex0 _ (True_atom _)  = hc_sty_id trueS
    printLatex0 _ (False_atom _) = hc_sty_id falseS
    printLatex0 ga (Predication p l _) =
        let (p_id,isQual) =
                case p of
                       Pred_name i          -> (i,False)
                       Qual_pred_name i _ _ -> (i,True)
            p' = printLatex0 ga p
        in if isQual then
             print_prefix_appl_latex ga p' l
           else condPrint_Mixfix_latex ga p_id l
    printLatex0 ga (Definedness f _) = hc_sty_id defS <\+> printLatex0 ga f
    printLatex0 ga (Existl_equation f g _) =
        hang_latex (printLatex0 ga f <\+> exequal_latex) 8
                       $ printLatex0 ga g
    printLatex0 ga (Strong_equation f g _) =
        hang_latex (printLatex0 ga f <\+> equals_latex) 8
                       $ printLatex0 ga g
    printLatex0 ga (Membership f g _) =
        printLatex0 ga f <\+> hc_sty_axiom "\\in" <\+> printLatex0 ga g
    printLatex0 ga (Mixfix_formula t) = printLatex0 ga t
    printLatex0 _ (Unparsed_formula _ _) = error "Unparsed_formula"
    printLatex0 ga (Sort_gen_ax constrs _) =
        hc_sty_id generatedS <>
        sp_braces_latex2 (hc_sty_id sortS <\+> commaT_latex ga sorts
                      <> semi_latex <\+> semiT_latex ga ops)
        <\+>(if null sortMap then empty
             else hc_sty_id withS
              <\+> fsep_latex (punctuate comma_latex
                               (map printSortMap sortMap)))
        where
        (sorts,ops,sortMap) = recover_Sort_gen_ax constrs
        printSortMap (s1,s2) = printLatex0 ga s1 <\+> mapsto_latex
                               <\+> printLatex0 ga s2
    printLatex0 ga (ExtFORMULA f) = printLatex0 ga f

instance PrintLaTeX QUANTIFIER where
    printLatex0 _ Universal = forall_latex
    printLatex0 _ Existential = exists_latex
    printLatex0 _ Unique_existential = unique_latex

instance PrintLaTeX PRED_SYMB where
    printLatex0 ga (Pred_name n) = printLatex0 ga n
    printLatex0 ga (Qual_pred_name n t _) =
        parens_latex $ hc_sty_id predS
                         <\+> printLatex0 ga n
                         <\+> colon_latex <\+> printLatex0 ga t

instance PrintLaTeX f => PrintLaTeX (TERM f) where
    printLatex0 ga (Simple_id i) = printLatex0 ga i
    printLatex0 ga (Qual_var n t _) = -- HERE
        parens_latex $ hc_sty_id varS
                         <\+> printLatex0 ga n
                         <\+> colon_latex <\+> printLatex0 ga t
    printLatex0 ga (Application o l _) =
        let (o_id,isQual) =
                case o of
                       Op_name i          -> (i,False)
                       Qual_op_name i _ _ -> (i,True)
            o' = printLatex0 ga o
        in if isQual then
             print_prefix_appl_latex ga (parens_latex o') l
           else
               print_Literal_latex ga o_id l
    printLatex0 ga (Sorted_term t s _) =
        condParensSorted_term parens_latex t (printLatex0 ga t) <>
        colon_latex <\+> printLatex0 ga s
    printLatex0 ga (Cast  t s _) =
        printLatex0 ga t <\+> hc_sty_id asS <\+> printLatex0 ga s
    printLatex0 ga(Conditional u f v _) =
        hang_latex (printLatex0 ga u) 8 $
             sep_latex ((hc_sty_id whenS <\+> printLatex0 ga f):
                     [hc_sty_id elseS <\+> printLatex0 ga v])
    printLatex0 _ (Unparsed_term _ _) = error "Unparsed_term"
    printLatex0 ga (Mixfix_qual_pred p) = printLatex0 ga p
    printLatex0 ga (Mixfix_term l) = listSep_latex space_latex ga l
    printLatex0 ga (Mixfix_token t) = printLatex0 ga t
    printLatex0 ga (Mixfix_sorted_term s _) = colon_latex
                                             <> printLatex0 ga s
    printLatex0 ga (Mixfix_cast s _) = hc_sty_id asS
                                     <\+> printLatex0 ga s
    printLatex0 ga (Mixfix_parenthesized l _) =
        parens_tab_latex (commaT_latex ga l)
    printLatex0 ga (Mixfix_bracketed l _) =
        brackets_latex (commaT_latex ga l)
    printLatex0 ga (Mixfix_braced l _) =
        sp_braces_latex2 (commaT_latex ga l)

instance PrintLaTeX OP_SYMB where
    printLatex0 ga (Op_name o) = printLatex0 ga o
    printLatex0 ga (Qual_op_name o t _) =
          hc_sty_id opS
           <\+> printLatex0 ga o <\+> colon_latex <> printLatex0 ga t

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

condPrint_Mixfix_latex :: PrintLaTeX f => GlobalAnnos -> Id -> [TERM f] -> Doc
condPrint_Mixfix_latex ga =
    condPrint_Mixfix (printLatex0 ga) (printLatex0 ga) (printLatex0 ga)
                     parens_tab_latex
                     (<\+>) fsep_latex comma_latex
                     (Just $ printDisplayToken_latex casl_axiom_latex)
                     (Just DF_LATEX) ga

print_prefix_appl_latex :: PrintLaTeX f => GlobalAnnos -> Doc -> [TERM f]
                        -> Doc
print_prefix_appl_latex ga =
    print_prefix_appl (printLatex0 ga) parens_tab_latex fsep_latex comma_latex

print_Literal_latex :: PrintLaTeX f => GlobalAnnos -> Id -> [TERM f] -> Doc
print_Literal_latex ga =
    print_Literal (printLatex0 ga) (printLatex0 ga) (printLatex0 ga)
                  parens_tab_latex
                  (<\+>) fsep_latex comma_latex
                  (Just $ printDisplayToken_latex casl_axiom_latex)
                  (Just DF_LATEX) ga

hc_sty_sig_item_keyword :: GlobalAnnos -> String -> Doc
hc_sty_sig_item_keyword ga str =
    (if is_inside_gen_arg ga then hc_sty_plain_keyword
                             else hc_sty_casl_keyword ) str
