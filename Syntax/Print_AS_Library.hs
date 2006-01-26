{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

pretty printing for heterogenous libraries in HetCASL.
-}

module Syntax.Print_AS_Library where

import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import Common.GlobalAnnotations
import Common.Keywords

import qualified Syntax.AS_Structured as AS_Struct
import Syntax.AS_Library
import Common.AS_Annotation

import Syntax.Print_AS_Architecture()
import Syntax.Print_AS_Structured

instance PrettyPrint LIB_DEFN where
    printText0 ga (Lib_defn aa ab _ ad) =
        let aa' = printText0 ga aa              -- lib name
            ab' = vsep $ map (printText0 ga) ab -- LIB_ITEMs
            ad' = vcat $ map (printText0 ga) ad -- global ANNOTATIONs
        in text libraryS <+> aa' $++$ ad' $++$ ab'

instance PrettyPrint LIB_ITEM where
    printText0 ga (Spec_defn aa ab ac _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
            spec_head = text specS <+> aa' <+> ab' <+> equals
            ac' = spAnnotedPrint (printText0 ga) (printText0 ga) (<+>)
                  (spec_head) ac
         -- nesting is done by the instance for SPEC now
        in ac' $$ text endS

    printText0 ga (View_defn aa ab ac ad _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
            -- ac' = printText0 ga ac
            (frm,to) = case ac of
                       AS_Struct.View_type vaa vab _ ->
                           (printGroupSpec ga vaa,
                            printGroupSpec ga vab)
            ad' = commaT_text ga ad
            eq' = if null ad then empty else equals
        in (hang (hang (hang (hang (text viewS <+> aa' <+> ab')
                                   6
                                   (colon <+> frm <+> text toS))
                             4
                             to)
                       2
                       eq')
                 4
                 ad')
           $$ text endS

    printText0 ga (Arch_spec_defn aa ab _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
        in (hang (text archS <+> text specS <+> aa' <+> equals) 4 ab')
               $$ text endS
    printText0 ga (Unit_spec_defn aa ab _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
        in (hang (text unitS <+> text specS <+> aa' <+> equals) 4 ab')
               $$ text endS
    printText0 ga (Ref_spec_defn aa ab _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
        in (hang (text refinementS <+> aa' <+> equals) 4 ab')
               $$ text endS
    printText0 ga (Download_items aa ab _) =
        let aa' = printText0 ga aa
            ab' = commaT_text ga ab
        in (hang (text fromS <+> aa' <+> text getS) 4 ab')
    printText0 ga (Syntax.AS_Library.Logic_decl aa _) =
        printLogicEncoding ga aa

condBracesGroupSpec4View_defn ::
    (GlobalAnnos -> (Annoted AS_Struct.SPEC) -> Doc)
        -> (Doc -> Doc) -- ^ a function enclosing the Doc
                        -- in braces
        -> GlobalAnnos -> (Annoted AS_Struct.SPEC) -> Doc
condBracesGroupSpec4View_defn pf b_fun ga as =
    case skip_Group $ item as of
                 AS_Struct.Spec_inst _ _ _ -> as'
                 AS_Struct.Union _ _       -> nested'
                 AS_Struct.Extension _ _   -> nested'
                 _                         -> nested'

    where nested' = b_fun as'
          as' = pf ga as

instance PrettyPrint ITEM_NAME_OR_MAP where
    printText0 ga (Item_name aa) =
        let aa' = printText0 ga aa
        in aa'
    printText0 ga (Item_name_map aa ab _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
        in aa' <+> text mapsTo <+> ab'

instance PrettyPrint LIB_NAME where
    printText0 ga (Lib_version aa ab) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
        in aa' <+> text versionS <+> ab'
    printText0 ga (Lib_id aa) =
        printText0 ga aa

instance PrettyPrint LIB_ID where
    printText0 _ (Direct_link aa _) =
        text aa
    printText0 _ (Indirect_link aa _) =
        text aa

instance PrettyPrint VERSION_NUMBER where
    printText0 _ (Version_number aa _) =
        hcat $ punctuate (char '.') $ map text aa
