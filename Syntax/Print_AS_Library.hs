{- |
Module      :  $Header$
Description :  pretty printing of CASL specification libaries
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  GPLv2 or higher
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Pretty printing of CASL specification libaries
-}

module Syntax.Print_AS_Library () where

import Common.Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.LibName

import Syntax.AS_Structured
import Syntax.AS_Library
import Common.AS_Annotation

import Syntax.Print_AS_Architecture()
import Syntax.Print_AS_Structured

instance Pretty LIB_DEFN where
    pretty (Lib_defn aa ab _ ad) =
        let aa' = pretty aa            -- lib name
            ab' = vsep $ map pretty ab -- LIB_ITEMs
            ad' = vcat $ map pretty ad -- global ANNOTATIONs
        in (if aa == emptyLibName "" then empty else
               keyword libraryS <+> aa') $++$ ad' $++$ ab'

instance Pretty LIB_ITEM where
    pretty li = case li of
        Spec_defn si (Genericity aa@(Params pl) ab@(Imported il) _) ac' _ ->
            let las = l_annos ac'
                (sa, ac) = if startsWithSemanticAnno las then
                               (equals <+> annoDoc (head las),
                                ac' { l_annos = tail las })
                           else (equals, ac')
                x : r = case skipVoidGroup $ item ac of
                          Extension e@(_ : _) _ ->
                              printExtension $ moveAnnos ac e
                          Union u@(_ : _) _ ->
                              printUnion $ moveAnnos ac u
                          _ -> [pretty ac]
                spid = indexed (tokStr si)
                sphead = if null il then
                             if null pl then spid <+> sa
                             else cat [spid, printPARAMS aa <+> sa]
                         else sep [ cat [spid, printPARAMS aa]
                                  , printIMPORTED ab <+> sa]
             in if null (tokStr si) && null pl then pretty ac' else
                    vcat $ (topKey specS <+> vcat [sphead, x]) : r
                    ++ [keyword endS]
        View_defn si (Genericity aa@(Params pl) ab@(Imported il) _)
                      (View_type frm to _) ad _ ->
            let spid = structSimpleId si
                sphead = if null il then
                             if null pl then spid <+> colon
                             else cat [spid, printPARAMS aa <+> colon]
                         else sep [ cat [spid, printPARAMS aa]
                                  , printIMPORTED ab <+> colon]
            in topKey viewS <+>
               sep ([sphead, sep [ printGroupSpec frm <+> keyword toS
                                  , (if null ad then id else (<+> equals))
                                    $ printGroupSpec to]]
                       ++ [ppWithCommas ad])
                          $+$ keyword endS
        Arch_spec_defn si ab _ ->
            topKey archS <+>
                   fsep[keyword specS, structSimpleId si <+> equals, pretty ab]
                           $+$ keyword endS
        Unit_spec_defn si ab _ ->
            topKey unitS <+>
                   fsep[keyword specS, structSimpleId si <+> equals, pretty ab]
                           $+$ keyword endS
        Ref_spec_defn si ab _ ->
            keyword refinementS <+>
                    fsep[structSimpleId si <+> equals, pretty ab]
                            $+$ keyword endS
        Download_items l ab _ ->
            topKey fromS <+> fsep ((pretty l <+> keyword getS)
                                   : punctuate comma (map pretty ab))
        Syntax.AS_Library.Logic_decl aa _ ->
            keyword logicS <+> pretty aa
        Syntax.AS_Library.Newlogic_defn nl _ ->
            pretty nl        

instance Pretty GENERICITY where
    pretty (Genericity aa ab _) = sep [printPARAMS aa, printIMPORTED ab]

printPARAMS :: PARAMS -> Doc
printPARAMS (Params aa) = cat $ map (brackets . rmTopKey . pretty ) aa

printIMPORTED :: IMPORTED -> Doc
printIMPORTED (Imported aa) = case aa of
    [] -> empty
    _  -> sep [ keyword givenS
              , sepByCommas $ map printGroupSpec aa]

instance Pretty ITEM_NAME_OR_MAP where
    pretty l = case l of
        Item_name aa -> structSimpleId aa
        Item_name_map aa ab _ ->
            fsep [structSimpleId aa, mapsto, structSimpleId ab]
