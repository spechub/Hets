{- |
Module      :  $Header$
Description :  pretty print abstract syntax of CoCASL
Copyright   :  (c) T. Mossakowski, Uni Bremen 2004-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hausmann@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

printing AS_CoCASL and CoCASLSign data types
-}

module CoCASL.Print_AS where

import Common.Keywords
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils

import CASL.AS_Basic_CASL
import CASL.ToDoc

import CoCASL.AS_CoCASL
import CoCASL.CoCASLSign

instance Pretty C_BASIC_ITEM where
    pretty = printC_BASIC_ITEM

printC_BASIC_ITEM :: C_BASIC_ITEM -> Doc
printC_BASIC_ITEM cb = case cb of
    CoFree_datatype l _ -> keyword cofreeS <+> printAnnotedCoDatas l
    CoSort_gen l _ -> case l of
      [Annoted (Ext_SIG_ITEMS (CoDatatype_items l' _)) _ _ _] ->
        keyword cogeneratedS <+> printAnnotedCoDatas l'
      _ -> keyword cogeneratedS <+> specBraces (vcat $ map pretty l)

printAnnotedCoDatas :: [Annoted CODATATYPE_DECL] -> Doc
printAnnotedCoDatas l = keyword (cotypeS ++ appendS l)
      <+> semiAnnos printCODATATYPE_DECL l

instance Pretty C_SIG_ITEM where
    pretty = printC_SIG_ITEM

printC_SIG_ITEM :: C_SIG_ITEM -> Doc
printC_SIG_ITEM (CoDatatype_items l _) = printAnnotedCoDatas l

instance Pretty CODATATYPE_DECL where
    pretty = printCODATATYPE_DECL

printCODATATYPE_DECL :: CODATATYPE_DECL -> Doc
printCODATATYPE_DECL (CoDatatype_decl s a _) = case a of
      [] -> idDoc s
      _ -> fsep [idDoc s, defn, sep $ punctuate (space <> bar) $
                      map (printAnnoted printCOALTERNATIVE) a]

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
                <> case k of
                   Total -> empty
                   _ -> quMarkD
    CoSubsorts l _ -> text (sortS ++ pluralS l) <+> ppWithCommas l

instance Pretty COCOMPONENTS where
    pretty = printCOCOMPONENTS

printCOCOMPONENTS :: COCOMPONENTS -> Doc
printCOCOMPONENTS (CoSelect l s _) =
    fsep (punctuate comma $ map idDoc l) <> colon <> pretty s

instance FormExtension C_FORMULA where
  isQuantifierLike f = case f of
    BoxOrDiamond {} -> False
    CoSort_gen_ax {} -> True

instance Pretty C_FORMULA where
    pretty = printC_FORMULA

printC_FORMULA :: C_FORMULA -> Doc
printC_FORMULA cf = case cf of
    BoxOrDiamond b t f _ ->
      let sp = case t of
                 Simple_mod _ -> (<>)
                 _ -> (<+>)
          td = printMODALITY t
          fd = printFormula f
      in if b then brackets td <> fd else less `sp` td `sp` greater <+> fd
    CoSort_gen_ax sorts ops _ -> keyword cogeneratedS <>
         specBraces (sep [ keyword sortS <+> ppWithCommas sorts <> semi
                         , fsep $ punctuate semi $ map pretty ops])

instance Pretty MODALITY where
    pretty = printMODALITY

printMODALITY :: MODALITY -> Doc
printMODALITY md = case md of
    Simple_mod ident -> sidDoc ident
    Term_mod t -> printTerm t

instance Pretty CoCASLSign where
    pretty = printCoCASLSign

printCoCASLSign :: CoCASLSign -> Doc
printCoCASLSign _ = empty
