{- |
Module      :  $Header$
Description :  pretty printing of CASL specification libaries
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Pretty printing of CASL specification libaries
-}

module Syntax.Print_AS_Library () where

import Data.Maybe (maybeToList)

import Common.IRI
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.LibName

import Syntax.AS_Structured
import Syntax.AS_Library
import Common.AS_Annotation

import Syntax.Print_AS_Architecture ()
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
                spid = indexed (iriToStringShortUnsecure si)
                sphead = if null il then
                             if null pl then spid <+> sa
                             else cat [spid, printPARAMS aa <+> sa]
                         else sep [ cat [spid, printPARAMS aa]
                                  , printIMPORTED ab <+> sa]
             in if null (iriToStringShortUnsecure si) && null pl
                then pretty ac' else
                    vcat $ (topKey specS <+> vcat [sphead, x]) : r
                    ++ [keyword endS]
        View_defn si (Genericity aa@(Params pl) ab@(Imported il) _)
                      (View_type frm to _) ad _ ->
            let spid = structIRI si
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
        Align_defn si ar (Align_type frm to _) corresps _ ->
            let spid = indexed (iriToStringShortUnsecure si)
                sphead = case ar of
                  Nothing -> spid <+> colon
                  Just alignArities -> sep [spid, printAlignArities alignArities
                                                  <+> colon ]
            in topKey alignmentS <+>
               (sep ([sphead, sep [ printGroupSpec frm <+> keyword toS,
                                    printGroupSpec to]]
                     ++ if null corresps then []
                        else [equals,
                              printCorrespondences corresps]))
               $+$ keyword endS
        Arch_spec_defn si ab _ ->
            topKey archS <+>
                   fsep [keyword specS, structIRI si <+> equals, pretty ab]
                           $+$ keyword endS
        Unit_spec_defn si ab _ ->
            topKey unitS <+>
                   fsep [keyword specS, structIRI si <+> equals, pretty ab]
                           $+$ keyword endS
        Ref_spec_defn si ab _ ->
            keyword refinementS <+>
                    fsep [structIRI si <+> equals, pretty ab]
                            $+$ keyword endS
        Download_items l ab _ ->
            topKey fromS <+> fsep ((pretty l <+> keyword getS)
                                   : prettyDownloadItems ab)
        Logic_decl aa _ -> sep [keyword logicS, pretty aa]
        Newlogic_defn nl _ ->
            pretty nl
        Newcomorphism_defn nc _ ->
            pretty nc

prettyDownloadItems :: DownloadItems -> [Doc]
prettyDownloadItems d = case d of
  ItemMaps l -> punctuate comma $ map pretty l
  UniqueItem i -> [mapsto, structIRI i]

instance Pretty GENERICITY where
    pretty (Genericity aa ab _) = sep [printPARAMS aa, printIMPORTED ab]

printPARAMS :: PARAMS -> Doc
printPARAMS (Params aa) = cat $ map (brackets . rmTopKey . pretty ) aa

printIMPORTED :: IMPORTED -> Doc
printIMPORTED (Imported aa) = case aa of
    [] -> empty
    _ -> sep [keyword givenS, sepByCommas $ map printGroupSpec aa]

printAlignArities :: ALIGN_ARITIES -> Doc
printAlignArities (Align_arities f b) =
  sep [text alignArityForwardS, printAlignArity f,
       text alignArityBackwardS, printAlignArity b]

printAlignArity :: ALIGN_ARITY -> Doc
printAlignArity AA_InjectiveAndTotal        = text "1"
printAlignArity AA_Injective                = text "?"
printAlignArity AA_Total                    = text "+"
printAlignArity AA_NeitherInjectiveNorTotal = text "*"

printCorrespondences :: [CORRESPONDENCE] -> Doc
printCorrespondences = vsep . (punctuate comma) . (map printCorrespondence)

printCorrespondence :: CORRESPONDENCE -> Doc
printCorrespondence Default_correspondence              = text "*"
printCorrespondence (Correspondence_block mrref mconf cs) =
  sep $ concat
  [[text relationS],
   map printRelationRef $ maybeToList mrref,
   map printConfidence $ maybeToList mconf,
   [text "{"],
   [printCorrespondences cs],
   [text "}"]]
       
printCorrespondence (Single_correspondence mcid eRef toer mrRef mconf) =
  sep $ concat
  [[indexed $ iriToStringShortUnsecure eRef],
   map printRelationRef $ maybeToList mrRef,
   map printConfidence $ maybeToList mconf,
   [case toer of
       -- TODO: implement (parser doesn't exist, either)
       Term _ _ -> undefined
       Entity_ref i -> indexed $ iriToStringShortUnsecure i],
   map pretty $ maybeToList mcid]

printConfidence :: CONFIDENCE -> Doc
   -- "show" should work in [0,1]
printConfidence = text . ('(':) . (++ ")") . show

printRelationRef :: RELATION_REF -> Doc
printRelationRef Subsumes        = text ">"
printRelationRef IsSubsumed      = text "<"
printRelationRef Equivalent      = text "="
printRelationRef Incompatible    = text "%"
printRelationRef HasInstance     = text "$\\ni$"
printRelationRef InstanceOf      = text "$\\in$"
printRelationRef DefaultRelation = text "$\\mapsto$"
printRelationRef (Iri i)         = indexed $ iriToStringShortUnsecure i

instance Pretty ItemNameMap where
    pretty (ItemNameMap a m) = fsep
       $ structIRI a : case m of
          Nothing -> []
          Just b -> [mapsto, structIRI b]
