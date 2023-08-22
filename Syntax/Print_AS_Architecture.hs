{- |
Module      :  ./Syntax/Print_AS_Architecture.hs
Description :  pretty printing of CASL architectural specifications
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Pretty printing of CASL architectural specifications
-}

module Syntax.Print_AS_Architecture () where

import Common.Doc
import Common.DocUtils
import Common.Keywords

import Syntax.AS_Architecture
import Syntax.Print_AS_Structured

sp1 :: Doc
sp1 = keyword " "

instance PrettyLG ARCH_SPEC where
    prettyLG lg a = case a of
        Basic_arch_spec aa ab _ -> sep [keyword (unitS ++ sS)
                <+> vcat (punctuate semi $ map (prettyLG lg) aa)
               , keyword resultS <+> prettyLG lg ab]
        Arch_spec_name aa -> pretty aa
        Group_arch_spec aa _ -> specBraces . rmTopKey $ prettyLG lg aa

instance PrettyLG UNIT_REF where
    prettyLG lg (Unit_ref aa ab _) =
        fsep [structIRI aa, keyword toS, prettyLG lg ab]

instance PrettyLG UNIT_DECL_DEFN where
    prettyLG lg ud = case ud of
        Unit_decl aa ab ac _ -> cat [structIRI aa <+> colon,
            sp1 <> fsep (prettyLG lg ab :
                 if null ac then [] else
                     keyword givenS : punctuate comma (map (prettyLG lg) ac))]
        Unit_defn aa ab _ ->
            cat [structIRI aa <+> equals, sp1 <> prettyLG lg ab]

instance PrettyLG UNIT_SPEC where
    prettyLG lg u = case u of
        Unit_type aa ab _ ->
          let ab' = rmTopKey $ printGroupSpec lg ab
          in if null aa then ab' else sep
               [ fsep . punctuate (space <> cross)
                          $ map (rmTopKey . printGroupSpec lg) aa
               , funArrow <+> ab']
        Spec_name aa -> pretty aa
        Closed_unit_spec aa _ -> fsep [keyword closedS, prettyLG lg aa]

instance PrettyLG REF_SPEC where
    prettyLG lg rs = case rs of
        Unit_spec u -> prettyLG lg u
        Refinement b u m r _ -> fsep $
            prettyLG lg u : (if b then [] else [keyword behaviourallyS])
            ++ [keyword refinedS]
            ++ (if null m then [] else keyword viaS :
                punctuate comma (map pretty m))
            ++ [keyword toS, prettyLG lg r]
        Arch_unit_spec aa _ ->
            fsep [keyword archS <+> keyword specS, prettyLG lg aa]
        Compose_ref aa _ -> case aa of
            [] -> empty
            x : xs -> sep $ prettyLG lg x :
               map ( \ s -> keyword thenS <+> prettyLG lg s) xs
        Component_ref aa _ ->
            specBraces $ sepByCommas $ map (prettyLG lg) aa

instance PrettyLG UNIT_EXPRESSION where
    prettyLG lg (Unit_expression aa ab _) =
        let ab' = prettyLG lg ab
        in if null aa then ab'
           else fsep $ keyword lambdaS :
                    punctuate semi (map (prettyLG lg) aa)
                    ++ [addBullet ab']

instance PrettyLG UNIT_BINDING where
    prettyLG lg (Unit_binding aa ab _) =
        let aa' = structIRI aa
            ab' = prettyLG lg ab
        in fsep [aa', colon, ab']

instance PrettyLG UNIT_TERM where
    prettyLG lg ut = case ut of
        Unit_reduction aa ab ->
          let aa' = prettyLG lg aa
              ab' = pretty ab
          in fsep [aa', ab']
        Unit_translation aa ab ->
          let aa' = prettyLG lg aa
              ab' = pretty ab
          in fsep [aa', ab']
        Amalgamation aa _ -> case aa of
            [] -> empty
            x : xs -> sep $ prettyLG lg x :
               map ( \ s -> keyword andS <+> prettyLG lg s) xs
        Local_unit aa ab _ ->
            fsep $ keyword localS : punctuate semi (map (prettyLG lg) aa)
                        ++ [keyword withinS, prettyLG lg ab]
        Unit_appl aa ab _ -> fsep $ structIRI aa : map (prettyLG lg) ab
        Group_unit_term aa _ -> specBraces $ prettyLG lg aa

instance PrettyLG FIT_ARG_UNIT where
    prettyLG lg (Fit_arg_unit aa ab _) = brackets $
        fsep $ prettyLG lg aa : if null ab then []
               else keyword fitS : punctuate comma (map pretty ab)
