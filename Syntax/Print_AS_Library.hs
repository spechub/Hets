{- |
Module      :  ./Syntax/Print_AS_Library.hs
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

import Common.AS_Annotation
import Common.IRI
import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.LibName

import Logic.Grothendieck

import Syntax.AS_Structured
import Syntax.AS_Library

import Syntax.Print_AS_Architecture ()
import Syntax.Print_AS_Structured

instance PrettyLG LIB_DEFN where
    prettyLG lg (Lib_defn aa ab _ ad) =
        let aa' = pretty aa            -- lib name
            ab' = vsep $ printLibItems lg ab -- LIB_ITEMs
            ad' = vcat $ map pretty ad -- global ANNOTATIONs
        in (if getLibId aa == nullIRI then empty else
               keyword libraryS <+> aa') $++$ ad' $++$ ab'

printLibItems :: LogicGraph -> [Annoted LIB_ITEM] -> [Doc]
printLibItems lg is = case is of
  [] -> []
  i : rs -> prettyLG lg i : printLibItems (case item i of
    Logic_decl aa _ -> setLogicName aa lg
    _ -> lg) rs

instance PrettyLG VIEW_TYPE where
  prettyLG = prettyViewType []

prettyViewType :: [a] -> LogicGraph -> VIEW_TYPE -> Doc
prettyViewType ad lg (View_type frm to _) =
  sep [ printGroupSpec lg frm <+> keyword toS
      , (if null ad then id else (<+> equals))
      $ printGroupSpec lg to]

instance PrettyLG LIB_ITEM where
    prettyLG lg li = case li of
        Spec_defn si (Genericity aa@(Params pl) ab@(Imported il) _) ac' _ ->
            let las = l_annos ac'
                (sa, ac) = if startsWithSemanticAnno las then
                               (equals <+> annoDoc (head las),
                                ac' { l_annos = tail las })
                           else (equals, ac')
                x : r = case skipVoidGroup $ item ac of
                          Extension e@(_ : _) _ ->
                              printExtension lg $ moveAnnos ac e
                          Union u@(_ : _) _ ->
                              printUnion lg $ moveAnnos ac u
                          _ -> [prettyLG lg ac]
                spid = indexed (iriToStringShortUnsecure si)
                sphead = if null il then
                             if null pl then spid <+> sa
                             else cat [spid, printPARAMS lg aa <+> sa]
                         else sep [ cat [spid, printPARAMS lg aa]
                                  , printIMPORTED lg ab <+> sa]
             in if null (iriToStringShortUnsecure si) && null pl
                then prettyLG lg ac' else
                    vcat $ (topKey specS <+> vcat [sphead, x]) : r
                    ++ [keyword endS]
        View_defn si (Genericity aa@(Params pl) ab@(Imported il) _)
                      vt ad _ ->
            let spid = structIRI si
                sphead = if null il then
                             if null pl then spid <+> colon
                             else cat [spid, printPARAMS lg aa <+> colon]
                         else sep [ cat [spid, printPARAMS lg aa]
                                  , printIMPORTED lg ab <+> colon]
            in topKey viewS <+>
               sep [sphead, prettyViewType ad lg vt, ppWithCommas ad]
               $+$ keyword endS
        Entail_defn si et _ -> topKey entailmentS <+>
            sep ((structIRI si <+> equals) : case et of
                 Entail_type s1 s2 _ ->
                   [ prettyLG lg s1
                   , keyword entailsS
                   , prettyLG lg s2 ]
                 OMSInNetwork i nw s2 _ ->
                   [ structIRI i <+> keyword inS
                   , pretty nw
                   , keyword entailsS
                   , prettyLG lg s2 ])
            $+$ keyword endS
        Equiv_defn si (Equiv_type as1 as2 _) sp _ -> topKey equivalenceS <+>
            sep [structIRI si <+> colon, sep
                [ prettyLG lg as1
                , text equiS
                , prettyLG lg as2]
                <+> equals, prettyLG lg sp]
            $+$ keyword endS
        Align_defn si ar vt corresps aSem _ ->
            let spid = indexed (iriToStringShortUnsecure si)
                sphead = case ar of
                  Nothing -> spid <+> colon
                  Just alignArities -> sep
                    [spid, printAlignArities alignArities <+> colon ]
            in topKey alignmentS <+>
               sep ([sphead, prettyViewType [] lg vt]
                     ++ if null corresps then []
                        else [ equals <+> printCorrespondences corresps
                             , keyword "assuming" <+> keyword (show aSem)])
               $+$ keyword endS
        Module_defn mn mt rs _ ->
            let spid = indexed (iriToStringShortUnsecure mn)
                sphead = spid <+> colon
                spmt = case mt of
                  Module_type sp1 sp2 _ -> sep
                    [prettyLG lg sp1, text ofS, prettyLG lg sp2]
            in topKey moduleS <+>
               sep [sphead, spmt, text forS, pretty rs]
        Query_defn qn vs sen spec mt _ -> topKey "query" <+>
            fsep ([ structIRI qn <+> equals
                  , keyword selectS <+> pretty vs
                  , keyword whereS <+> pretty sen
                  , keyword inS <+> prettyLG lg spec]
                  ++ maybe []
                  (\ r -> [keyword "along" <+> pretty r]) mt)
            $+$ keyword endS
        Subst_defn sn vt sm _ -> topKey "substitution" <+>
            sep [ structIRI sn <+> colon, prettyViewType [] lg vt
                , equals <+> pretty sm]
            $+$ keyword endS
        Result_defn rn sl sq b _ -> topKey resultS <+>
            fsep ([ structIRI rn , ppWithCommas sl
                  , keyword forS <+> pretty sq]
                  ++ [keyword "%complete" | b])
            $+$ keyword endS
        Arch_spec_defn si ab _ -> topKey archS <+>
            fsep [keyword specS, structIRI si <+> equals, prettyLG lg ab]
            $+$ keyword endS
        Unit_spec_defn si ab _ -> topKey unitS <+>
            fsep [keyword specS, structIRI si <+> equals, prettyLG lg ab]
            $+$ keyword endS
        Ref_spec_defn si ab _ -> keyword refinementS <+>
            fsep [structIRI si <+> equals, prettyLG lg ab]
            $+$ keyword endS
        Network_defn si n _ -> keyword networkS <+>
            fsep [structIRI si <+> equals, pretty n]
            $+$ keyword endS
        Download_items l ab _ -> topKey fromS <+>
            fsep ((pretty l <+> keyword getS) : prettyDownloadItems ab)
        Logic_decl aa _ -> pretty aa
        Newlogic_defn nl _ -> pretty nl
        Newcomorphism_defn nc _ -> pretty nc

instance PrettyLG OmsOrNetwork where
   prettyLG lg s = case s of
     MkOms o -> printGroupSpec lg o
     MkNetwork n -> pretty n

prettyDownloadItems :: DownloadItems -> [Doc]
prettyDownloadItems d = case d of
  ItemMaps l -> punctuate comma $ map pretty l
  UniqueItem i -> [mapsto, structIRI i]

instance PrettyLG GENERICITY where
    prettyLG lg (Genericity aa ab _) =
        sep [printPARAMS lg aa, printIMPORTED lg ab]

printPARAMS :: LogicGraph -> PARAMS -> Doc
printPARAMS lg (Params aa) = cat $ map (brackets . rmTopKey . prettyLG lg ) aa

printIMPORTED :: LogicGraph -> IMPORTED -> Doc
printIMPORTED lg (Imported aa) = case aa of
    [] -> empty
    _ -> sep [keyword givenS, sepByCommas $ map (printGroupSpec lg) aa]

instance Pretty ALIGN_ARITIES where
  pretty = printAlignArities

printAlignArities :: ALIGN_ARITIES -> Doc
printAlignArities (Align_arities f b) =
  sep [text alignArityForwardS, printAlignArity f,
       text alignArityBackwardS, printAlignArity b]

printAlignArity :: ALIGN_ARITY -> Doc
printAlignArity = text . showAlignArity

printCorrespondences :: [CORRESPONDENCE] -> Doc
printCorrespondences = vsep . punctuate comma . map printCorrespondence

printCorrespondence :: CORRESPONDENCE -> Doc
printCorrespondence Default_correspondence = text "*"
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
  [[indexed $ show eRef],
   map printRelationRef $ maybeToList mrRef,
   map printConfidence $ maybeToList mconf,
   [pretty toer],
   map pretty $ maybeToList mcid]

instance Pretty CORRESPONDENCE where
  pretty = printCorrespondence

printConfidence :: CONFIDENCE -> Doc
   -- "show" should work in [0,1]
printConfidence = text . ('(' :) . (++ ")") . show

printRelationRef :: RELATION_REF -> Doc
printRelationRef rref = case rref of
  Subsumes -> greater
  IsSubsumed -> less
  Equivalent -> equals
  Incompatible -> text "%"
  HasInstance -> keyword "ni"
  InstanceOf -> keyword "in"
  DefaultRelation -> mapsto
  Iri i -> structIRI i

instance Pretty ItemNameMap where
    pretty (ItemNameMap a m) = fsep
       $ structIRI a : case m of
          Nothing -> []
          Just b -> [mapsto, structIRI b]
