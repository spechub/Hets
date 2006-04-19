{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

pretty printing data types of 'BASIC_SPEC'
-}

-- to do: remove the "Dangerous hack"

module CASL.Print_AS_Basic where

import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Print_AS_Annotation
import Common.Keywords
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import qualified Common.Doc as Doc

import CASL.AS_Basic_CASL
import CASL.ToDoc

instance (PrettyPrint b, PrettyPrint s, PrettyPrint f) =>
    PrettyPrint (BASIC_SPEC b s f) where
    printText0 ga = Doc.toText ga . 
         printBASIC_SPEC (fromText ga) (fromText ga) (fromText ga)

instance (PrettyPrint b, PrettyPrint s, PrettyPrint f) =>
    PrettyPrint (BASIC_ITEMS b s f) where
    printText0 ga = Doc.toText ga . 
         printBASIC_ITEMS (fromText ga) (fromText ga) (fromText ga)


printFormulaAux :: PrettyPrint f => GlobalAnnos -> [Annoted (FORMULA f)] -> Doc
printFormulaAux ga f =
  vcat $ map (printAnnotedFormula_Text0 ga True) f

printAnnotedFormula_Text0 :: PrettyPrint f =>
                             GlobalAnnos -> Bool -> Annoted (FORMULA f) -> Doc
printAnnotedFormula_Text0 ga withDot = Doc.toText ga . Doc.printAnnoted 
           ((if withDot then (Doc.bullet Doc.<+>) else id) . fromText ga)

instance (PrettyPrint s, PrettyPrint f) => PrettyPrint (SIG_ITEMS s f) where
    printText0 ga = Doc.toText ga . printSIG_ITEMS (fromText ga) (fromText ga) 


instance PrettyPrint f => PrettyPrint (SORT_ITEM f) where
    printText0 ga = Doc.toText ga . printSortItem (fromText ga)

instance PrettyPrint f => PrettyPrint (OP_ITEM f) where
    printText0 ga = Doc.toText ga . printOpItem (fromText ga)

optQuMark :: FunKind -> Doc
optQuMark Partial = text quMark
optQuMark Total = empty

instance PrettyPrint OP_TYPE where
    printText0 = toText

instance PrettyPrint OP_HEAD where
    printText0 = toText

instance PrettyPrint ARG_DECL where
    printText0 ga = Doc.toText ga . printArgDecl

instance PrettyPrint f => PrettyPrint (OP_ATTR f) where
    printText0 ga = Doc.toText ga . printAttr (fromText ga)

instance PrettyPrint f => PrettyPrint (PRED_ITEM f) where
    printText0 ga = Doc.toText ga . printPredItem (fromText ga)

instance PrettyPrint PRED_TYPE where
    printText0 = toText

instance PrettyPrint PRED_HEAD where
    printText0 ga = Doc.toText ga . printPredHead

instance PrettyPrint DATATYPE_DECL where
    printText0 = toText

instance PrettyPrint ALTERNATIVE where
    printText0 = toText

instance PrettyPrint COMPONENTS where
    printText0 = toText


toText :: Doc.Pretty a => GlobalAnnos -> a -> Doc
toText ga = Doc.toText ga . Doc.pretty

instance PrettyPrint VAR_DECL where
    printText0 = toText

printFORMULA :: PrettyPrint f => GlobalAnnos -> FORMULA f -> Doc
printFORMULA ga = Doc.toText ga . printFormula (fromText ga)

printTheoryFormula :: PrettyPrint f => GlobalAnnos -> Named (FORMULA f) -> Doc
printTheoryFormula ga f = printAnnotedFormula_Text0 ga
    (case sentence f of
    Quantification Universal _ _ _ -> False
    Sort_gen_ax _ _ -> False
    _ -> True) $ Doc.fromLabelledSen f 

instance PrettyPrint f => PrettyPrint (FORMULA f) where
    printText0 = printFORMULA

instance PrettyPrint PRED_SYMB where
    printText0 = toText

instance PrettyPrint f => PrettyPrint (TERM f) where
    printText0 ga = Doc.toText ga . printTerm (fromText ga)

instance PrettyPrint OP_SYMB where
    printText0 = toText

instance PrettyPrint SYMB_ITEMS where
    printText0 ga (Symb_items k l _) =
        print_kind_text k l <+> commaT_text ga l

instance PrettyPrint SYMB_MAP_ITEMS where
    printText0 ga (Symb_map_items k l _) =
        print_kind_text k l <+> commaT_text ga l

print_kind_text :: SYMB_KIND -> [a] -> Doc
print_kind_text k l = case k of
    Implicit -> empty
    _ -> text (pluralS_symb_list k l)

pluralS_symb_list :: SYMB_KIND -> [a] -> String
pluralS_symb_list k l = (case k of
    Implicit -> error "pluralS_symb_list"
    Sorts_kind -> sortS
    Ops_kind   -> opS
    Preds_kind -> predS) ++ (if isSingle l then "" else "s")

instance PrettyPrint SYMB_KIND where
    printText0 _ k = print_kind_text k [()]

instance PrettyPrint SYMB where
    printText0 ga (Symb_id i) = printText0 ga i
    printText0 ga (Qual_id i t _) =
        printText0 ga i <+> colon <+> printText0 ga t

instance PrettyPrint TYPE where
    printText0 ga (O_type t) = printText0 ga t
    printText0 ga (P_type t) = printText0 ga t
    printText0 ga (A_type t) = printText0 ga t

instance PrettyPrint SYMB_OR_MAP where
    printText0 ga (Symb s) = printText0 ga s
    printText0 ga (Symb_map s t _) =
        printText0 ga s <+> text mapsTo <+> printText0 ga t


