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
import Common.PrettyPrint
import Common.PPUtils
import CASL.Print_AS_Basic
import CoCASL.AS_CoCASL
import CoCASL.CoCASLSign
import Common.AS_Annotation
import CASL.AS_Basic_CASL
import Common.Doc
import CASL.ToDoc
import Common.Id

instance PrettyPrint C_BASIC_ITEM where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty C_BASIC_ITEM where
    pretty = printC_BASIC_ITEM

printC_BASIC_ITEM :: C_BASIC_ITEM -> Doc
printC_BASIC_ITEM cb = case cb of
    CoFree_datatype l _ -> text cofreeS <+> text (cotypeS ++ pluralS l)
      <+> (fsep $ punctuate semi $ map (printAnnoted printCODATATYPE_DECL) l)
    CoSort_gen l _ -> case l of
      [Annoted (Ext_SIG_ITEMS (CoDatatype_items l' _)) _ _ _] -> 
        keyword cogeneratedS <+> keyword (cotypeS ++ pluralS l') <+>
         semiAnnos printCODATATYPE_DECL l'
      _ -> keyword cogeneratedS <+> 
           (specBraces $ vcat $ map pretty l)

instance PrettyPrint C_SIG_ITEM where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty C_SIG_ITEM where
    pretty = printC_SIG_ITEM

printC_SIG_ITEM :: C_SIG_ITEM -> Doc
printC_SIG_ITEM (CoDatatype_items l _) =
    text (cotypeS ++ pluralS l) <+>
     (fsep $ punctuate semi $ map (printAnnoted printCODATATYPE_DECL) l)

instance PrettyPrint CODATATYPE_DECL where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty CODATATYPE_DECL where
    pretty = printCODATATYPE_DECL

printCODATATYPE_DECL :: CODATATYPE_DECL -> Doc
printCODATATYPE_DECL (CoDatatype_decl s a _) = case a of
      [] -> idDoc s
      _ -> fsep [idDoc s, defn, sep $ punctuate (space <> bar) $ 
                      map (printAnnoted printCOALTERNATIVE) a]

instance PrettyPrint COALTERNATIVE where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty COALTERNATIVE where
    pretty = printCOALTERNATIVE

printCOALTERNATIVE :: COALTERNATIVE -> Doc 
printCOALTERNATIVE coal = case coal of
    Co_construct k n l _ -> case n of
       Nothing -> empty
       Just i -> idDoc i
       <> (case l of
        [] -> case k of
              Total -> empty
              _ -> parens empty
        _ -> parens (fsep $ punctuate semi $ map printCOCOMPONENTS l)) 
                <> case  k of
                   Total -> empty
                   _ -> text quMark
        
    CoSubsorts l _ -> fsep $ text (sortS ++ if isSingle l then "" else "s") 
                            : punctuate comma (map idDoc l)
      

instance PrettyPrint COCOMPONENTS where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty COCOMPONENTS where
    pretty = printCOCOMPONENTS


printCOCOMPONENTS :: COCOMPONENTS -> Doc
printCOCOMPONENTS (CoSelect l s _) = 
   (fsep $ punctuate comma $ map idDoc l)
    <> colon
    <> printOpType s

instance PrettyPrint C_FORMULA where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty C_FORMULA where
    pretty = printC_FORMULA

printC_FORMULA :: C_FORMULA -> Doc
printC_FORMULA cf = case cf of
    BoxOrDiamond b t f _ -> let sp = case t of
                                 Simple_mod _ -> (<>)
                                 _ -> (<+>)
                                td = printMODALITY t
                                fd = printFormula printC_FORMULA f
                            in if b then brackets td <> fd
                              else text lessS `sp` td `sp` text greaterS <+> fd     
    CoSort_gen_ax sorts ops _ -> text cogeneratedS <>
         specBraces (text sortS <+> 
           (fsep $ punctuate comma $ map idDoc sorts) <> semi <+>
           (fsep $ punctuate semi $ map printOpSymb ops))  
    

instance PrettyPrint MODALITY where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty MODALITY where
    pretty = printMODALITY

printMODALITY :: MODALITY -> Doc
printMODALITY mod = case mod of
    Simple_mod ident -> sidDoc ident
    Term_mod t -> printTerm printC_FORMULA t

instance PrettyPrint CoCASLSign where
    printText0 = CASL.Print_AS_Basic.toText

instance Pretty CoCASLSign where
    pretty = printCoCASLSign

printCoCASLSign :: CoCASLSign -> Doc  
printCoCASLSign _ = empty

instance ListCheck CODATATYPE_DECL where
    innerList (CoDatatype_decl _ _ _) = [()]
