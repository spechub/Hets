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
import CASL.ToDoc
import qualified Common.Doc as Doc
import Common.DocUtils
import Common.GlobalAnnotations
import Common.LaTeX_AS_Annotation
import Common.Keywords
import Common.Lib.Pretty (Doc, empty)
import Common.PrintLaTeX (PrintLaTeX(..))
import Common.LaTeX_utils

instance (PrintLaTeX b, PrintLaTeX s, PrintLaTeX f)
    => PrintLaTeX (BASIC_SPEC b s f) where
    printLatex0 ga = Doc.toLatex ga . 
        printBASIC_SPEC (fromLatex ga) (fromLatex ga) (fromLatex ga)
        
instance (PrintLaTeX b, PrintLaTeX s, PrintLaTeX f) =>
         PrintLaTeX (BASIC_ITEMS b s f) where
    printLatex0 ga = Doc.toLatex ga . 
        printBASIC_ITEMS (fromLatex ga) (fromLatex ga) (fromLatex ga) 

instance (PrintLaTeX s, PrintLaTeX f) =>
          PrintLaTeX (SIG_ITEMS s f) where
    printLatex0 ga = Doc.toLatex ga .
        printSIG_ITEMS (fromLatex ga) (fromLatex ga) 

instance PrintLaTeX f => PrintLaTeX (SORT_ITEM f) where
    printLatex0 ga = Doc.toLatex ga . printSortItem (fromLatex ga)

instance PrintLaTeX f => PrintLaTeX (OP_ITEM f) where
    printLatex0 ga = Doc.toLatex ga . printOpItem (fromLatex ga)

instance PrintLaTeX OP_TYPE where
    printLatex0 = toOldLatex

optLatexQuMark :: FunKind -> Doc
optLatexQuMark Partial = hc_sty_axiom quMark
optLatexQuMark Total = empty

instance PrintLaTeX OP_HEAD where
    printLatex0 = toOldLatex

instance PrintLaTeX ARG_DECL where
    printLatex0 ga = Doc.toLatex ga . printArgDecl

instance PrintLaTeX f => PrintLaTeX (OP_ATTR f) where
    printLatex0 ga = Doc.toLatex ga . printAttr (fromLatex ga)

instance PrintLaTeX f => PrintLaTeX (PRED_ITEM f) where
    printLatex0 ga = Doc.toLatex ga . printPredItem (fromLatex ga)

instance PrintLaTeX PRED_TYPE where
    printLatex0 = toOldLatex

instance PrintLaTeX PRED_HEAD where
    printLatex0 ga = Doc.toLatex ga . printPredHead

instance PrintLaTeX DATATYPE_DECL where
    printLatex0 = toOldLatex

instance PrintLaTeX ALTERNATIVE where
    printLatex0 = toOldLatex

instance PrintLaTeX COMPONENTS where
    printLatex0 = toOldLatex

instance PrintLaTeX VAR_DECL where
    printLatex0 = toOldLatex

instance PrintLaTeX f => PrintLaTeX (FORMULA f) where
    printLatex0 ga = Doc.toLatex ga . printFormula (fromLatex ga)

instance PrintLaTeX PRED_SYMB where
    printLatex0 = toOldLatex

instance PrintLaTeX f => PrintLaTeX (TERM f) where
    printLatex0 ga = Doc.toLatex ga . printTerm (fromLatex ga)

instance PrintLaTeX OP_SYMB where
    printLatex0 = toOldLatex

instance PrintLaTeX SYMB_ITEMS where
    printLatex0 = toOldLatex

instance PrintLaTeX SYMB_MAP_ITEMS where
    printLatex0 = toOldLatex

instance PrintLaTeX SYMB_KIND where
    printLatex0 = toOldLatex

instance PrintLaTeX SYMB where
    printLatex0 = toOldLatex

instance PrintLaTeX TYPE where
    printLatex0 = toOldLatex

instance PrintLaTeX SYMB_OR_MAP where
    printLatex0 = toOldLatex

hc_sty_sig_item_keyword :: GlobalAnnos -> String -> Doc
hc_sty_sig_item_keyword ga str =
    (if is_inside_gen_arg ga then hc_sty_plain_keyword
                             else hc_sty_casl_keyword ) str
