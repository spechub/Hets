{- |
Module      :  ./Syntax/Print_AS_Structured.hs
Description :  pretty printing of CASL structured specifications
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Pretty printing of CASL structured specifications
-}

module Syntax.Print_AS_Structured
    ( structIRI
    , printGroupSpec
    , skipVoidGroup
    , printUnion
    , printExtension
    , moveAnnos
    , PrettyLG (..)
    ) where

import Common.Id
import Common.IRI
import Common.Keywords
import Common.Doc
import Common.DocUtils
import Common.AS_Annotation

import Logic.Grothendieck
import Logic.Logic

import Syntax.AS_Structured

sublogicId :: SIMPLE_ID -> Doc
sublogicId = structId . tokStr

structIRI :: IRI -> Doc
structIRI = structId . iriToStringShortUnsecure -- also print user information

class PrettyLG a where
  prettyLG :: LogicGraph -> a -> Doc

instance PrettyLG a => PrettyLG (Annoted a) where
    prettyLG lg = printAnnoted $ prettyLG lg

instance PrettyLG SPEC where
    prettyLG = printSPEC

printUnion :: LogicGraph -> [Annoted SPEC] -> [Doc]
printUnion lg = prepPunctuate (topKey andS <> space) . map (condBracesAnd lg)

printIntersection :: LogicGraph -> [Annoted SPEC] -> [Doc]
printIntersection lg = prepPunctuate (topKey intersectS <> space) . map (condBracesAnd lg)

moveAnnos :: Annoted SPEC -> [Annoted SPEC] -> [Annoted SPEC]
moveAnnos x l = appAnno $ case l of
    [] -> error "moveAnnos"
    h : r -> h { l_annos = l_annos x ++ l_annos h } : r
    where appAnno a = case a of
                 [] -> []
                 [h] -> [appendAnno h (r_annos x)]
                 h : r -> h : appAnno r

printOptUnion :: LogicGraph -> Annoted SPEC -> [Doc]
printOptUnion lg x = case skipVoidGroup $ item x of
        Union e@(_ : _) _ -> printUnion lg $ moveAnnos x e
        Extension e@(_ : _) _ -> printExtension lg $ moveAnnos x e
        _ -> [prettyLG lg x]

printExtension :: LogicGraph -> [Annoted SPEC] -> [Doc]
printExtension lg l = case l of
    [] -> []
    x : r -> printOptUnion lg x ++
             concatMap ((\ u -> case u of
                            [] -> []
                            d : s -> (topKey thenS <+> d) : s) .
                        printOptUnion lg) r

printSPEC :: LogicGraph -> SPEC -> Doc
printSPEC lg spec = case spec of
    Basic_spec (G_basic_spec lid basic_spec) _ ->
        case lookupCurrentSyntax "" lg of
      Just (Logic lid2, sm) -> if language_name lid2 /= language_name lid
          then error "printSPEC: logic mismatch"
          else case basicSpecPrinter sm lid of
        Just p -> p basic_spec
        _ -> error $ "printSPEC: no basic spec printer for "
             ++ showSyntax lid sm
      _ -> error "printSPEC: incomplete logic graph"
    EmptySpec _ -> specBraces empty
    Extraction aa ab -> sep [condBracesTransReduct lg aa, printEXTRACTION ab]
    Translation aa ab -> sep [condBracesTransReduct lg aa, printRENAMING ab]
    Reduction aa ab -> sep [condBracesTransReduct lg aa, printRESTRICTION ab]
    Approximation aa ab ->
      sep [condBracesTransReduct lg aa, printAPPROXIMATION ab]
    Minimization aa ab ->
      sep [condBracesTransReduct lg aa, printMINIMIZATION ab]
    Filtering aa ab -> sep [condBracesTransReduct lg aa, printFILTERING ab]
    Union aa _ -> sep $ printUnion lg aa
    Intersection aa _ -> sep $ printIntersection lg aa
    Extension aa _ -> sep $ printExtension lg aa
    Free_spec aa _ -> sep [keyword freeS, printGroupSpec lg aa]
    Cofree_spec aa _ -> sep [keyword cofreeS, printGroupSpec lg aa]
    Minimize_spec aa _ -> sep [keyword minimizeS, printGroupSpec lg aa]
    Local_spec aa ab _ -> fsep
      [keyword localS, prettyLG lg aa, keyword withinS, condBracesWithin lg ab]
    Closed_spec aa _ -> sep [keyword closedS, printGroupSpec lg aa]
    Group aa _ -> prettyLG lg aa
    Spec_inst aa ab mi _ -> let
      r = cat [structIRI aa, print_fit_arg_list lg ab]
      in maybe r (\ i -> sep [r, pretty i]) mi
    Qualified_spec ln asp _ -> pretty ln <> colon
      $+$ prettyLG (setLogicName ln lg) asp
    Data ld _ s1 s2 _ -> keyword dataS
        <+> printGroupSpec (setCurLogic (show ld) lg) s1
        $+$ prettyLG lg s2
    Combination n _ -> sep [keyword combineS, pretty n]
    Apply i bs _ ->
      sep [keyword "apply" <+> pretty i, prettyLG lg $ Basic_spec bs nullRange]
    Bridge s1 rs s2 _ -> fsep $ [condBraces lg s1, keyword "bridge"]
      ++ map pretty rs ++ [condBraces lg s2]
    Unsolved_IRI i -> keyword "unsolved iri"<+>pretty i

instance Pretty Network where
    pretty (Network cs es _) = fsep $ ppWithCommas cs
      : if null es then [] else [keyword excludingS, ppWithCommas es]

instance Pretty FILTERING where
    pretty = printFILTERING

printFILTERING :: FILTERING -> Doc
printFILTERING (FilterBasicSpec b aa _) =
   keyword (if b then selectS else rejectS) <+> pretty aa
printFILTERING (FilterSymbolList b aa _) =
   keyword (if b then selectS else rejectS) <+> pretty aa

instance Pretty MINIMIZATION where
    pretty = printMINIMIZATION

printMINIMIZATION :: MINIMIZATION -> Doc
printMINIMIZATION (Mini kw cms cvs _) =
   fsep $ keyword (tokStr kw) : map pretty cms ++ if null cvs then [] else
     keyword "vars" : map pretty cvs

instance Pretty APPROXIMATION where
    pretty = printAPPROXIMATION

printAPPROXIMATION :: APPROXIMATION -> Doc
printAPPROXIMATION (ForgetOrKeep b syms ml _) =
   fsep $ keyword (if b then forgetS else keepS)
   : ppWithCommas syms : maybe [] (\ i -> [keyword withS, pretty i]) ml

instance Pretty EXTRACTION where
    pretty = printEXTRACTION

printEXTRACTION :: EXTRACTION -> Doc
printEXTRACTION (ExtractOrRemove b aa _) =
   keyword (if b then "extract" else "remove") <+> fsep (map pretty aa)

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

instance PrettyLG FIT_ARG where
    prettyLG = printFIT_ARG

printFIT_ARG :: LogicGraph -> FIT_ARG -> Doc
printFIT_ARG lg fit = case fit of
    Fit_spec aa ab _ ->
        let aa' = rmTopKey $ prettyLG lg aa
        in if null ab then aa' else
               fsep $ aa' : keyword fitS
                        : punctuate comma (map printG_mapping ab)
    Fit_view si ab _ ->
        sep [keyword viewS, cat [structIRI si, print_fit_arg_list lg ab]]

instance Pretty Logic_code where
    pretty = printLogic_code

printLogic_code :: Logic_code -> Doc
printLogic_code (Logic_code menc msrc mtar _) =
   let pm = maybe [] ((: []) . printLogic_name) in
   fsep $ maybe [] ((: [colon]) . pretty) menc
        ++ pm msrc ++ funArrow : pm mtar

instance Pretty LogicDescr where
    pretty ld = case ld of
      LogicDescr n s _ -> sep [keyword logicS, pretty n,
        maybe empty (\ r -> sep [keyword serializationS, pretty r]) s]
      SyntaxQual i -> sep [keyword serializationS, pretty i]
      LanguageQual i -> sep [keyword "language", pretty i]

instance Pretty Logic_name where
    pretty = printLogic_name

printLogic_name :: Logic_name -> Doc
printLogic_name (Logic_name mlog slog ms) = let d = structId mlog in
    case slog of
      Nothing -> d
      Just sub -> d <> dot <> sublogicId sub
    <> maybe empty (parens . pretty) ms

instance Pretty LABELED_ONTO_OR_INTPR_REF where
    pretty = printLIRI

printLIRI :: LABELED_ONTO_OR_INTPR_REF -> Doc
printLIRI (Labeled n i) = case n of
    Just x -> pretty x <+> colon <+> pretty i
    Nothing -> pretty i

{- |
  specialized printing of 'FIT_ARG's
-}
print_fit_arg_list :: LogicGraph -> [Annoted FIT_ARG] -> Doc
print_fit_arg_list lg = cat . map (brackets . prettyLG lg)

{- |
   conditional generation of grouping braces for Union and Extension
-}
printGroupSpec :: LogicGraph -> Annoted SPEC -> Doc
printGroupSpec lg s = let d = prettyLG lg s in
    case skip_Group $ item s of
                 Spec_inst {} -> d
                 _ -> specBraces d

{- |
  generate grouping braces for Tanslations and Reductions
-}
condBracesTransReduct :: LogicGraph -> Annoted SPEC -> Doc
condBracesTransReduct lg s = let d = prettyLG lg s in
    case skip_Group $ item s of
                 Bridge {} -> specBraces d
                 Extension {} -> specBraces d
                 Union {} -> specBraces d
                 Intersection {} -> specBraces d
                 Local_spec {} -> specBraces d
                 _ -> d

{- |
  generate grouping braces for Within
-}
condBracesWithin :: LogicGraph -> Annoted SPEC -> Doc
condBracesWithin lg s = let d = prettyLG lg s in
    case skip_Group $ item s of
                 Bridge {} -> specBraces d
                 Extension {} -> specBraces d
                 Union {} -> specBraces d
                 Intersection {} -> specBraces d
                 _ -> d
{- |
  only Extensions inside of Unions (and) need grouping braces
-}
condBracesAnd :: LogicGraph -> Annoted SPEC -> Doc
condBracesAnd lg s = let d = prettyLG lg s in
    case skip_Group $ item s of
                 Bridge {} -> specBraces d
                 Extension {} -> specBraces d
                 _ -> d

-- bridges inside bridges need grouping
condBraces :: LogicGraph -> Annoted SPEC -> Doc
condBraces lg s = let d = prettyLG lg s in
    case skip_Group $ item s of
                 Bridge {} -> specBraces d
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
