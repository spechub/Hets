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
import Common.Print_AS_Annotation
import Common.GlobalAnnotations
import Common.LaTeX_AS_Annotation
import Common.Keywords
import Common.Lib.Pretty
import Common.PrintLaTeX
import Common.LaTeX_utils
import Common.PPUtils

import Data.Char (toUpper)

instance (PrintLaTeX b, PrintLaTeX s, PrintLaTeX f)
    => PrintLaTeX (BASIC_SPEC b s f) where
    printLatex0 ga (Basic_spec l) =
        if null l then braces_latex empty else vcat (map (printLatex0 ga) l)

instance (PrintLaTeX b, PrintLaTeX s, PrintLaTeX f) =>
         PrintLaTeX (BASIC_ITEMS b s f) where
    printLatex0 ga (Sig_items s) = printLatex0 ga s
    printLatex0 ga (Free_datatype l _) =
        fsep_latex [hc_sty_plain_keyword "free"
                    <~> setTab_latex
                    <> hc_sty_plain_keyword ("type"++ pluralS l)
                   ,tabbed_nest_latex $ semiAnno_latex ga l]
    printLatex0 ga (Sort_gen l _) =
        hang_latex (hc_sty_plain_keyword generatedS
                    <~> setTab_latex<> condTypeS) 9 $
                   tabbed_nest_latex $ condBraces
                                  (vcat (map (printLatex0 ga) l))
        where condTypeS =
                  if isOnlyDatatype then
                     hc_sty_plain_keyword (typeS++pluralS l)
                  else empty
              condBraces d =
                  if isOnlyDatatype then
                     case l of
                     [x] -> case x of
                            Annoted (Datatype_items l' _) _ lans _ ->
                                vcat (map (printLatex0 ga) lans)
                                         $$ semiAnno_latex ga l'
                            _ -> error "wrong implementation of isOnlyDatatype"
                     _ -> error "wrong implementation of isOnlyDatatype"
                  else braces_latex d
              isOnlyDatatype =
                  case l of
                  [x] -> case x of
                         Annoted (Datatype_items _ _) _ _ _ -> True
                         _ -> False
                  _  -> False
    printLatex0 ga (Var_items l _) =
        hc_sty_plain_keyword (varS++pluralS l) <\+>
        semiT_latex ga l
    printLatex0 ga (Local_var_axioms l f _) =
        hc_sty_axiom "\\forall" <\+> semiT_latex ga l
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
        let i'   = hc_sty_axiom "\\bullet"
                      <\+> set_tabbed_nest_latex (printLatex0 ga i)
            las' = if not $ null las then
                      sp_text 0 "\n" <> printAnnotationList_Latex0 ga las
                   else
                      empty
            (la,ras') =
                splitAndPrintRAnnos printLatex0
                                    printAnnotationList_Latex0
                                    (<\+>) (latex_macro "\\`" <>)
                                    empty ga ras
        in  {-trace (show i)-} (las' $+$ fsep_latex [i',la] $$ ras')

instance (PrintLaTeX s, PrintLaTeX f) =>
          PrintLaTeX (SIG_ITEMS s f) where
    printLatex0 ga (Sort_items l _) =
        hc_sty_sig_item_keyword ga  (sortS++pluralS l) <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)
    printLatex0 ga (Op_items l _) =
        hc_sty_sig_item_keyword ga (opS++pluralS l)   <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)
    printLatex0 ga (Pred_items l _) =
        hc_sty_sig_item_keyword ga (predS++pluralS l) <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)
    printLatex0 ga (Datatype_items l _) =
        hc_sty_sig_item_keyword ga (typeS++pluralS l) <\+>
        set_tabbed_nest_latex (semiAnno_latex ga l)
    printLatex0 ga (Ext_SIG_ITEMS s) = printLatex0 ga s

instance PrintLaTeX f => PrintLaTeX (SORT_ITEM f) where
    printLatex0 ga (Sort_decl l _) = commaT_latex ga l
    printLatex0 ga (Subsort_decl l t _) =
        hang_latex (commaT_latex ga l) 8 $
                   hc_sty_axiom lessS <\+> printLatex0 ga t
    printLatex0 ga (Subsort_defn s v t f _) =
        printLatex0 ga s <\+> equals_latex <\+>
           braces_latex (set_tabbed_nest_latex $ fsep
                            [printLatex0 ga v
                             <> colon_latex
                             <\+> printLatex0 ga t,
                             hc_sty_axiom "\\bullet"
                             <\+> set_tabbed_nest_latex (printLatex0 ga f)])
    printLatex0 ga (Iso_decl l _) =
        fsep_latex $ punctuate  (space_latex<>equals_latex) $
                   map (printLatex0 ga) l

instance PrintLaTeX f => PrintLaTeX (OP_ITEM f) where
    printLatex0 ga (Op_decl l t a _) =
        {-cat [ cat [commaT_latex ga l
                  ,colon_latex <> printLatex0 ga t <> condComma]
            , if na then empty
              else commaT_latex ga a
            ]-}
        if na then ids_sig
        else setTabWithSpaces_latex 4
                 <>
                 fsep [ids_sig,
                       tabbed_nest_latex $ commaT_latex ga a]
        where ids_sig = -- setTabWithSpaces_latex 6 <>
                         fsep [commaT_latex ga l<\+>colon_latex,
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
                                         hc_sty_axiom "\\rightarrow")
            result_type = printLatex0 ga s
        in if isEmpty arg_types then result_type
           else sep_latex [arg_types,type_arr <\+> result_type]

    printLatex0 ga (Op_type Partial l s _) =
        (if null l then hc_sty_axiom quMark
         else space_latex
              <> crossT_latex ga l
               <\+>hc_sty_axiom ("\\rightarrow" ++ quMark))
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
        printLatex0 ga s <\+>
        sep_latex
           (defnS'<> setTab_latex<~>
              (printLatex0 ga $ head a)<>casl_normal_latex "~":
            (map (\x -> tabbed_nest_latex (latex_macro
                                                 "\\hspace*{-0.84mm}"<> ---}
                                           casl_normal_latex "\\textbar")
                            <~> (printLatex0 ga x)<>casl_normal_latex "~") $
                 tail a))
        where defnS' = hc_sty_axiom defnS
instance PrintLaTeX ALTERNATIVE where
    printLatex0 ga (Alt_construct k n l _) = tabbed_nest_latex (
        printLatex0 ga n <> (if null l then case k of
                             Partial -> parens_tab_latex empty
                             _ -> empty
                            else parens_tab_latex ( semiT_latex ga l))
                            <> optLatexQuMark k)
    printLatex0 ga (Subsorts l _) =
        sp_text (axiom_width s') s'' <\+> commaT_latex ga l
        where s'  = sortS ++ pluralS l
              s'' = '\\':map toUpper s' ++ "[ID]"

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
             hc_sty_axiom "\\bullet"
                <\+> set_tabbed_nest_latex (printLatex0 ga f)]
    printLatex0 ga (Conjunction fs _) =
        sep_latex $ punctuate (space_latex <> hc_sty_axiom "\\wedge")
          $ map (condParensXjunction printLatex0 parens_tab_latex ga) fs
{-      (sep_latex $ prepand_head $
         prepPunctuate (hc_sty_axiom "\\wedge" <> space_latex) $
            map (condParensXjunction printLatex0 parens_tab_latex ga) fs)
        where prepand_head l = case l of
                               []     -> []
                               [x]    -> l
                               (x:xs) -> (hspace_latex "0.375cm"<>x) : xs-}
    printLatex0 ga (Disjunction  fs _) =
        sep_latex $ punctuate (space_latex <> hc_sty_axiom "\\vee")
          $ map (condParensXjunction printLatex0 parens_tab_latex ga) fs
{-      (sep_latex $ prepand_head $
       prepPunctuate (hc_sty_axiom "\\vee" <> space_latex) $
            map (condParensXjunction printLatex0 parens_tab_latex ga) fs)
        where prepand_head l = case l of
                               []     -> []
                               [x]    -> l
                               (x:xs) ->  (hspace_latex "0.375cm"<>x): xs-}
    printLatex0 ga i@(Implication f g b _) =
        {-trace pos $ -}
        if not b
        then (
        hang_latex (condParensImplEquiv printLatex0 parens_tab_latex ga i g False
                    <\+> hc_sty_id "if") 3 $
             condParensImplEquiv printLatex0 parens_tab_latex ga i f True)

        else (
        hang_latex (condParensImplEquiv printLatex0 parens_tab_latex ga i f False
                    <\+> hc_sty_axiom "\\Rightarrow") 3 $
             condParensImplEquiv printLatex0 parens_tab_latex ga i g True)
{-      where pos = "Implication: \"=>\": "++show p
                    ++"; left_most_id_of_first_formula: "
                    ++(show $ left_most_pos f )-}
    printLatex0 ga e@(Equivalence  f g _) =
        sep_latex
             [condParensImplEquiv printLatex0 parens_tab_latex ga e f False
                    <\+> hc_sty_axiom "\\Leftrightarrow",
              condParensImplEquiv printLatex0 parens_tab_latex ga e g True]
    printLatex0 ga (Negation f _) = hc_sty_axiom "\\neg" <\+> condParensNeg f parens_latex (printLatex0 ga f)
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
        hang_latex (printLatex0 ga f
                    <\+> sp_text (axiom_width "=")
                                 "\\Ax{\\stackrel{e}{=}}") 8
                       $ printLatex0 ga g
    printLatex0 ga (Strong_equation f g _) =
        hang_latex (printLatex0 ga f <\+> hc_sty_axiom "=") 8
                       $ printLatex0 ga g
    printLatex0 ga (Membership f g _) =
        printLatex0 ga f <\+> hc_sty_axiom "\\in" <\+> printLatex0 ga g
    printLatex0 ga (Mixfix_formula t) = printLatex0 ga t
    printLatex0 _ (Unparsed_formula s _) = text s
    printLatex0 ga (Sort_gen_ax constrs _) =
        hc_sty_id generatedS <>
        braces_latex (hc_sty_id sortS <+> commaT_latex ga sorts
                      <> semi_latex <+> semiT_latex ga ops)
        <+>(if null sortMap then empty
             else hc_sty_id withS
              <+> fsep_latex (punctuate comma_latex (map printSortMap sortMap)))
        where
        (sorts,ops,sortMap) = recover_Sort_gen_ax constrs
        printSortMap (s1,s2) = printLatex0 ga s1 <+> hc_sty_axiom "\\mapsto"
                               <+> printLatex0 ga s2
    printLatex0 ga (ExtFORMULA f) = printLatex0 ga f

instance PrintLaTeX QUANTIFIER where
    printLatex0 _ (Universal) = hc_sty_axiom "\\forall"
    printLatex0 _ (Existential) = hc_sty_axiom "\\exists"
    printLatex0 _ (Unique_existential) = hc_sty_axiom "\\exists!"

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
    printLatex0 _ (Unparsed_term s _) = text s
    printLatex0 ga (Mixfix_qual_pred p) = printLatex0 ga p
    printLatex0 ga (Mixfix_term l) =
        cat(punctuate space (map (printLatex0 ga) l))
    printLatex0 ga (Mixfix_token t) = printLatex0 ga t
    printLatex0 ga (Mixfix_sorted_term s _) = colon
                                             <> printLatex0 ga s
    printLatex0 ga (Mixfix_cast s _) = text asS
                                     <\+> printLatex0 ga s
    printLatex0 ga (Mixfix_parenthesized l _) =
        parens_tab_latex (commaT_latex ga l)
    printLatex0 ga (Mixfix_bracketed l _) =
        brackets_latex (commaT_latex ga l)
    printLatex0 ga (Mixfix_braced l _) =
        braces_latex (commaT_latex ga l)

instance PrintLaTeX OP_SYMB where
    printLatex0 ga (Op_name o) = printLatex0 ga o
    printLatex0 ga (Qual_op_name o t _) =
          hc_sty_id opS
           <\+> printLatex0 ga o <\+> colon_latex <> printLatex0 ga t

instance PrintLaTeX SYMB_ITEMS where
    printLatex0 ga (Symb_items k l _) =
        print_kind_latex ga k l <\+> commaT_latex ga l

instance PrintLaTeX SYMB_MAP_ITEMS where
    printLatex0 ga (Symb_map_items k l _) =
        print_kind_latex ga k l <\+> commaT_latex ga l

instance PrintLaTeX SYMB_KIND where
    printLatex0 _ Implicit   = empty
    printLatex0 _ Sorts_kind = casl_keyword_latex sortS
    printLatex0 _ Ops_kind   = casl_keyword_latex opS
    printLatex0 _ Preds_kind = casl_keyword_latex predS

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
        printLatex0 ga s <\+> hc_sty_axiom "\\mapsto" <\+> printLatex0 ga t

print_kind_latex :: GlobalAnnos -> SYMB_KIND -> [a] -> Doc
print_kind_latex ga k l =
    case k of
    Implicit -> empty
    _        -> latex_macro "\\KW{"<>kw<>s<>latex_macro "}"
    where kw = printLatex0 ga k
          s  = case pluralS_symb_list k l of
               "" -> empty
               s' -> casl_keyword_latex s'

condPrint_Mixfix_latex :: PrintLaTeX f => GlobalAnnos -> Id -> [TERM f] -> Doc
condPrint_Mixfix_latex ga =
    condPrint_Mixfix (printLatex0 ga) (printLatex0 ga) (printLatex0 ga)
                     parens_tab_latex
                     (<\+>) fsep_latex comma_latex
                     (Just $ printDisplayToken_latex casl_axiom_latex)
                     (Just DF_LATEX) ga

print_prefix_appl_latex :: PrintLaTeX f => GlobalAnnos -> Doc -> [TERM f] -> Doc
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
