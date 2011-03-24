{- |
Module      :  $Header$
Description :  pretty printing of CASL structured specifications
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Pretty printing of CASL structured specifications
-}

module Syntax.Print_AS_Structured
    ( structSimpleId
    , printGroupSpec
    , skipVoidGroup
    , printUnion
    , printExtension
    , moveAnnos
    ) where

import Common.Id
import Common.Keywords
import Common.Doc
import Common.DocUtils
import Common.AS_Annotation

import Logic.Grothendieck ()

import Syntax.AS_Structured

structSimpleId :: SIMPLE_ID -> Doc
structSimpleId = structId . tokStr

instance Pretty SPEC where
    pretty = printSPEC

printUnion :: [Annoted SPEC] -> [Doc]
printUnion = prepPunctuate (topKey andS <> space) . map condBracesAnd

moveAnnos :: Annoted SPEC -> [Annoted SPEC] -> [Annoted SPEC]
moveAnnos x l = appAnno $ case l of
    [] -> error "moveAnnos"
    h : r -> h { l_annos = l_annos x ++ l_annos h } : r
    where appAnno a = case a of
                 [] -> []
                 [h] -> [appendAnno h (r_annos x)]
                 h : r -> h : appAnno r

printOptUnion :: Annoted SPEC -> [Doc]
printOptUnion x = case skipVoidGroup $ item x of
        Union e@(_ : _) _ -> printUnion $ moveAnnos x e
        Extension e@(_ : _) _ -> printExtension $ moveAnnos x e
        _ -> [pretty x]

printExtension :: [Annoted SPEC] -> [Doc]
printExtension l = case l of
    [] -> []
    x : r -> printOptUnion x ++
             concatMap (( \ u -> case u of
                            [] -> []
                            d : s -> (topKey thenS <+> d) : s) .
                        printOptUnion) r

printSPEC :: SPEC -> Doc
printSPEC spec = case spec of
    Basic_spec aa _ -> pretty aa
    EmptySpec _ -> specBraces empty
    Translation aa ab -> sep [condBracesTransReduct aa, printRENAMING ab]
    Reduction aa ab -> sep [condBracesTransReduct aa, printRESTRICTION ab]
    Union aa _ -> sep $ printUnion aa
    Extension aa _ -> sep $ printExtension aa
    Free_spec aa _ -> sep [keyword freeS, printGroupSpec aa]
    Cofree_spec aa _ -> sep [keyword cofreeS, printGroupSpec aa]
    Local_spec aa ab _ -> fsep
        [keyword localS, pretty aa, keyword withinS, condBracesWithin ab]
    Closed_spec aa _ -> sep [keyword closedS, printGroupSpec aa]
    Group aa _ -> pretty aa
    Spec_inst aa ab _ -> cat [structSimpleId aa, print_fit_arg_list ab]
    Qualified_spec ln asp _ -> printLogicEncoding ln <> colon $+$ pretty asp
    Data _ _ s1 s2 _ -> keyword dataS <+> printGroupSpec s1 $+$ pretty s2

instance Pretty RENAMING where
    pretty = printRENAMING

printRENAMING :: RENAMING -> Doc
printRENAMING (Renaming aa _) =
   keyword withS <+> ppWithCommas aa

instance Pretty RESTRICTION where
    pretty = printRESTRICTION

printRESTRICTION :: RESTRICTION -> Doc
printRESTRICTION rest = case rest of
    Hidden aa _ -> keyword hideS <+> ppWithCommas aa
    Revealed aa _ -> keyword revealS <+> pretty aa

printLogicEncoding :: (Pretty a) => a -> Doc
printLogicEncoding enc = keyword logicS <+> pretty enc

instance Pretty G_mapping where
    pretty = printG_mapping

printG_mapping :: G_mapping -> Doc
printG_mapping gma = case gma of
    G_symb_map gsmil -> pretty gsmil
    G_logic_translation enc -> printLogicEncoding enc

instance Pretty G_hiding where
    pretty = printG_hiding

printG_hiding :: G_hiding -> Doc
printG_hiding ghid = case ghid of
    G_symb_list gsil -> pretty gsil
    G_logic_projection enc -> printLogicEncoding enc

instance Pretty FIT_ARG where
    pretty = printFIT_ARG

printFIT_ARG :: FIT_ARG -> Doc
printFIT_ARG fit = case fit of
    Fit_spec aa ab _ ->
        let aa' = rmTopKey $ pretty aa
        in if null ab then aa' else
               fsep $ aa' : keyword fitS
                        : punctuate comma (map printG_mapping ab)
    Fit_view si ab _ ->
        sep [keyword viewS, cat [structSimpleId si, print_fit_arg_list ab]]

instance Pretty Logic_code where
    pretty = printLogic_code

printLogic_code :: Logic_code -> Doc
printLogic_code (Logic_code menc msrc mtar _) =
   let pm = maybe [] ((: []) . printLogic_name) in
   fsep $ maybe [] ((: [colon]) . pretty) menc
        ++ pm msrc ++ funArrow : pm mtar

instance Pretty Logic_name where
    pretty = printLogic_name

printLogic_name :: Logic_name -> Doc
printLogic_name (Logic_name mlog slog) = let d = structSimpleId mlog in
    case slog of
      Nothing -> d
      Just sub -> d <> dot <> structSimpleId sub

{- |
  specialized printing of 'FIT_ARG's
-}
print_fit_arg_list :: [Annoted FIT_ARG] -> Doc
print_fit_arg_list = cat . map (brackets . pretty)

{- |
   conditional generation of grouping braces for Union and Extension
-}
printGroupSpec :: Annoted SPEC -> Doc
printGroupSpec s = let d = pretty s in
    case skip_Group $ item s of
                 Spec_inst _ _ _ -> d
                 _ -> specBraces d

{- |
  generate grouping braces for Tanslations and Reductions
-}
condBracesTransReduct :: Annoted SPEC -> Doc
condBracesTransReduct s = let d = pretty s in
    case skip_Group $ item s of
                 Extension _ _ -> specBraces d
                 Union _ _ -> specBraces d
                 Local_spec _ _ _ -> specBraces d
                 _ -> d

{- |
  generate grouping braces for Within
-}
condBracesWithin :: Annoted SPEC -> Doc
condBracesWithin s = let d = pretty s in
    case skip_Group $ item s of
                 Extension _ _ -> specBraces d
                 Union _ _ -> specBraces d
                 _ -> d
{- |
  only Extensions inside of Unions (and) need grouping braces
-}
condBracesAnd :: Annoted SPEC -> Doc
condBracesAnd s = let d = pretty s in
    case skip_Group $ item s of
                 Extension _ _ -> specBraces d
                 _ -> d

-- | only skip groups without annotations
skipVoidGroup :: SPEC -> SPEC
skipVoidGroup sp =
    case sp of
            Group g _ | null (l_annos g) && null (r_annos g)
                          -> skipVoidGroup $ item g
            _ -> sp

-- | skip nested groups
skip_Group :: SPEC -> SPEC
skip_Group sp =
    case sp of
            Group g _ -> skip_Group $ item g
            _ -> sp
