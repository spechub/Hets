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
import Common.Lib.Pretty (Doc, empty, (<>), ($$), fcat, vcat)
import Common.PrintLaTeX (PrintLaTeX(..))
import Common.LaTeX_utils
import Common.PPUtils (pluralS)

instance (PrintLaTeX b, PrintLaTeX s, PrintLaTeX f)
    => PrintLaTeX (BASIC_SPEC b s f) where
    printLatex0 ga = Doc.toLatex ga . 
        printBASIC_SPEC (fromLatex ga) (fromLatex ga) (fromLatex ga)
        

instance (PrintLaTeX b, PrintLaTeX s, PrintLaTeX f) =>
         PrintLaTeX (BASIC_ITEMS b s f) where
    printLatex0 ga = Doc.toLatex ga . 
        printBASIC_ITEMS (fromLatex ga) (fromLatex ga) (fromLatex ga) 

printLatex0Axioms :: PrintLaTeX f =>
               GlobalAnnos -> [Annoted (FORMULA f)] -> Doc
printLatex0Axioms ga = vcat . map (printAnnotedFormula_Latex0 ga)

printAnnotedFormula_Latex0 :: PrintLaTeX f =>
               GlobalAnnos -> Annoted (FORMULA f) -> Doc
printAnnotedFormula_Latex0 ga =
    Doc.toLatex ga . Doc.printAnnoted 
           ((Doc.bullet Doc.<+>) . printFormula (fromLatex ga))

instance (PrintLaTeX s, PrintLaTeX f) =>
          PrintLaTeX (SIG_ITEMS s f) where
    printLatex0 ga = Doc.toLatex ga .
        printSIG_ITEMS (fromLatex ga) (fromLatex ga) 

instance PrintLaTeX f => PrintLaTeX (SORT_ITEM f) where
    printLatex0 ga = Doc.toLatex ga . printSortItem (fromLatex ga)

instance PrintLaTeX f => PrintLaTeX (OP_ITEM f) where
    printLatex0 ga = Doc.toLatex ga . printOpItem (fromLatex ga)

instance PrintLaTeX OP_TYPE where
    printLatex0 = toLatex

optLatexQuMark :: FunKind -> Doc
optLatexQuMark Partial = hc_sty_axiom quMark
optLatexQuMark Total = empty

instance PrintLaTeX OP_HEAD where
    printLatex0 = toLatex

instance PrintLaTeX ARG_DECL where
    printLatex0 ga = Doc.toLatex ga . printArgDecl

instance PrintLaTeX f => PrintLaTeX (OP_ATTR f) where
    printLatex0 ga = Doc.toLatex ga . printAttr (fromLatex ga)

instance PrintLaTeX f => PrintLaTeX (PRED_ITEM f) where
    printLatex0 ga = Doc.toLatex ga . printPredItem (fromLatex ga)

instance PrintLaTeX PRED_TYPE where
    printLatex0 = toLatex

instance PrintLaTeX PRED_HEAD where
    printLatex0 ga = Doc.toLatex ga . printPredHead

instance PrintLaTeX DATATYPE_DECL where
    printLatex0 = toLatex

instance PrintLaTeX ALTERNATIVE where
    printLatex0 = toLatex

instance PrintLaTeX COMPONENTS where
    printLatex0 = toLatex


instance PrintLaTeX VAR_DECL where
    printLatex0 = toLatex

instance PrintLaTeX f => PrintLaTeX (FORMULA f) where
    printLatex0 ga = Doc.toLatex ga . printFormula (fromLatex ga)

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
