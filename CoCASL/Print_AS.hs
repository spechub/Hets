{- |
Module      :  $Header$
Copyright   :  (c) T. Mossakowski, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hausmann@tzi.de
Stability   :  provisional
Portability :  portable

printing AS_CoCASL and CoCASLSign data types
-}

module CoCASL.Print_AS where

import Common.Keywords
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import CASL.Print_AS_Basic
import CoCASL.AS_CoCASL
import CoCASL.CoCASLSign
import Common.AS_Annotation
import CASL.AS_Basic_CASL

instance PrettyPrint C_BASIC_ITEM where
    printText0 ga (CoFree_datatype l _) =
        hang (text cofreeS <+> text (cotypeS ++ pluralS l)) 4 $
             semiAnno_text ga l
    printText0 ga (CoSort_gen l _) =
        case l of
        [Annoted (Ext_SIG_ITEMS (CoDatatype_items l' _)) _ lans _] ->
            hang (text cogeneratedS <+> text (cotypeS ++ pluralS l')) 4
                 (vcat (map (printText0 ga) lans)
                          $$ semiAnno_text ga l')
        _ -> hang (text cogeneratedS) 4 $
             braces $ vcat $ map (printText0 ga) l

instance PrettyPrint C_SIG_ITEM where
    printText0 ga (CoDatatype_items l _) =
        text (cotypeS ++ pluralS l) <+> semiAnno_text ga l

instance PrettyPrint CODATATYPE_DECL where
    printText0 ga (CoDatatype_decl s a _) =
        printText0 ga s <> case a of
          [] -> error "PrettyPrint CoCASL.CODATATYPE_DECL"
          h : t -> sep $ hang (text defnS) 4 (printText0 ga h) :
              map (\x -> nest 2 $ text barS <+> nest 2 (printText0 ga x)) t

instance PrettyPrint COALTERNATIVE where
    printText0 ga (Co_construct k n l _) = printText0 ga n
                                 <> (if null l then case k of
                                                   Total -> empty
                                                   _ -> parens empty
                                    else parens(semiT_text ga l)) <>
                                         optQuMark k
    printText0 ga (CoSubsorts l _) = text sortS <+> commaT_text ga l

instance PrettyPrint COCOMPONENTS where
    printText0 ga (CoSelect l s _) = commaT_text ga l
                                <> colon
                                <> printText0 ga s


instance PrettyPrint C_FORMULA where
    printText0 ga (BoxOrDiamond b t f _) =
        let sp = case t of
                         Simple_mod _ -> (<>)
                         _ -> (<+>)
            td = printText0 ga t
            fd = printText0 ga f
        in if b then brackets td <> fd
           else text lessS `sp` td `sp` text greaterS <+> fd
    printText0 ga (CoSort_gen_ax sorts ops _) =
        text cogeneratedS <>
        braces (text sortS <+> commaT_text ga sorts
                <> semi <+> semiT_text ga ops)

instance PrettyPrint MODALITY where
    printText0 ga (Simple_mod ident) =
         printText0 ga ident
    printText0 ga (Term_mod t) = printText0 ga t

instance PrettyPrint CoCASLSign where
    printText0 _ga _s = empty

instance ListCheck CODATATYPE_DECL where
    innerList (CoDatatype_decl _ _ _) = [()]
