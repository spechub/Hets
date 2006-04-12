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
    printText0 ga (Basic_spec l) =
        if null l then braces empty else vcat (map (printText0 ga) l)

instance (PrettyPrint b, PrettyPrint s, PrettyPrint f) =>
    PrettyPrint (BASIC_ITEMS b s f) where
    printText0 ga (Sig_items s) = printText0 ga s
    printText0 ga (Free_datatype l _) =
        hang (text freeS <+> text (typeS ++ pluralS l)) 4 $
             semiAnno_text ga l
    printText0 ga (Sort_gen l _) = case l of
        [Annoted (Datatype_items l' _) _ lans _] ->
            hang (text generatedS <+> text (typeS ++ pluralS l')) 4
                 (vcat (map (printText0 ga) lans)
                          $$ semiAnno_text ga l')
        _ -> hang (text generatedS) 4 $
             braces $ vcat $ map (printText0 ga) l
    printText0 ga (Var_items l _) =
        text (varS ++ pluralS l) <+> semiT_text ga l
    printText0 ga (Local_var_axioms l f _) =
        text forallS <+> semiT_text ga l
                 $$ printFormulaAux ga f
    printText0 ga (Axiom_items f _) =
        printFormulaAux ga f
    printText0 ga (Ext_BASIC_ITEMS b) = printText0 ga b

printFormulaAux :: PrettyPrint f => GlobalAnnos -> [Annoted (FORMULA f)] -> Doc
printFormulaAux ga f =
  vcat $ map (printAnnotedFormula_Text0 ga True) f

printAnnotedFormula_Text0 :: PrettyPrint f =>
                             GlobalAnnos -> Bool -> Annoted (FORMULA f) -> Doc
printAnnotedFormula_Text0 ga withDot = Doc.toText ga . Doc.printAnnoted 
           ((if withDot then (Doc.bullet Doc.<+>) else id) . fromText ga)

instance (PrettyPrint s, PrettyPrint f) =>
         PrettyPrint (SIG_ITEMS s f) where
    printText0 ga (Sort_items l _) =
        Doc.toText ga $ Doc.topKey (sortS ++ pluralS l) Doc.<+> 
             Doc.semiAnnos (printSortItem $ fromText ga) l
    printText0 ga (Op_items l _) =
        Doc.toText ga $ Doc.topKey (opS ++ pluralS l) Doc.<+> 
             Doc.semiAnnos (printOpItem $ fromText ga) l
    printText0 ga (Pred_items l _) = 
        Doc.toText ga $ Doc.topKey (predS ++ pluralS l) Doc.<+>
             Doc.semiAnnos (printPredItem $ fromText ga) l
    printText0 ga (Datatype_items l _) =
         Doc.toText ga $ Doc.topKey (typeS ++ pluralS l) Doc.<+>
             Doc.semiAnnos printDATATYPE_DECL l
    printText0 ga (Ext_SIG_ITEMS s) = printText0 ga s

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

---- instances of ListCheck for various data types of AS_Basic_CASL ---

instance ListCheck (SORT_ITEM f) where
    innerList (Sort_decl l _) = innerList l
    innerList (Subsort_decl l _ _) = innerList l
    innerList (Subsort_defn _ _ _ _ _) = [()]
    innerList (Iso_decl _ _) = [()]

instance ListCheck (OP_ITEM f) where
    innerList (Op_decl l _ _ _) = innerList l
    innerList (Op_defn _ _ _ _) = [()]

instance ListCheck (PRED_ITEM f) where
    innerList (Pred_decl l _ _) = innerList l
    innerList (Pred_defn _ _ _ _) = [()]

instance ListCheck DATATYPE_DECL where
    innerList (Datatype_decl _ _ _) = [()]

instance ListCheck VAR_DECL where
    innerList (Var_decl l _ _) = innerList l

-----------------------------------------------------------------------------
