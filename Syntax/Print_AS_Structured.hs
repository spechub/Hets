{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Printing the Structured part of hetrogenous specifications.
-}

module Syntax.Print_AS_Structured where

import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import Common.Keywords

import Logic.Grothendieck()

import Syntax.AS_Structured
import Common.AS_Annotation
import Common.GlobalAnnotations

instance PrettyPrint SPEC where
    --- This implementation doesn't use the grouping information
    --- it detects this information by precedence rules
    printText0 ga (Basic_spec aa) =
        nest 4 $ printText0 ga aa
    printText0 ga (Translation aa ab) =
        let aa' = condBracesTransReduct printText0 sp_braces ga aa
            ab' = printText0 ga ab
        in hang aa' 4 ab'
    printText0 ga (Reduction aa ab) =
        let aa' = condBracesTransReduct printText0 sp_braces ga aa
            ab' = printText0 ga ab
        in hang aa' 4 ab'
    printText0 ga (Union aa _) =
        fsep $ pl aa
        where pl [] = []
              pl (x:xs) =
                  (condBracesAnd printText0 sp_braces ga x):
                  map (\y -> text andS $$
                       condBracesAnd printText0 sp_braces ga y)
                      xs
    printText0 ga (Extension aa _) =
        fsep $ printList aa
        where printList [] = []
              printList (x:xs) =
                  (printText0 ga x):
                    map (spAnnotedPrint (printText0 ga)
                         (printText0 ga) (<+>) (text thenS)) xs
    printText0 ga (Free_spec aa _) =
        hang (text freeS) 5 $
             printGroupSpec ga aa
    printText0 ga (Cofree_spec aa _) =
        hang (text cofreeS) 5 $
             printGroupSpec ga aa
    printText0 ga (Local_spec aa ab _) =
        let aa' = printText0 ga aa
            ab' = condBracesWithin printText0 sp_braces ga ab
        in (hang (text localS) 4 aa') $$
           (hang (text withinS) 4 ab')
    printText0 ga (Closed_spec aa _) =
        hang (text closedS) 4 $
             printGroupSpec ga aa
    printText0 ga (Group aa _) =
        printText0 ga aa
    printText0 ga (Spec_inst aa ab _) =
        let aa' = printText0 ga aa
            ab' = print_fit_arg_list printText0 sp_brackets sep ga ab
        in nest 4 (hang aa' 4 ab')
    printText0 ga (Qualified_spec ln asp _) =
        printLogicEncoding ga ln <> colon $$ (printText0 ga asp)
    printText0 ga (Data _ _ s1 s2 _) =
        text dataS <+> (printText0 ga s1) $$ (printText0 ga s2)

printGroupSpec :: GlobalAnnos -> Annoted SPEC -> Doc
printGroupSpec = condBracesGroupSpec printText0 braces Nothing

instance PrettyPrint RENAMING where
    printText0 ga (Renaming aa _) =
        hang (text withS) 4 $ commaT_text ga aa

instance PrettyPrint RESTRICTION where
    printText0 ga (Hidden aa _) =
        hang (text hideS) 4 $ commaT_text ga aa
    printText0 ga (Revealed aa _) =
        hang (text revealS) 4 $ printText0 ga aa

condPunct :: Doc -> [G_hiding] -> [Doc] -> [Doc]
condPunct _ [] [] = []
condPunct _ _  [] =
    error "something went wrong in printLatex0 of Hidden"
condPunct _ [] _  =
    error "something went wrong in printLatex0 of Hidden"
condPunct _ [_c] [d] = [d]
condPunct com (c:cs) (d:ds) =
                 (case c of
                        G_symb_list _gsil -> d<>com
                        G_logic_projection _enc -> d)
                 : condPunct com cs ds

{- Is declared in Print_AS_Library
instance PrettyPrint SPEC_DEFN where
-}

printLogicEncoding :: (PrettyPrint a) => GlobalAnnos -> a -> Doc
printLogicEncoding ga enc = text logicS <+> printText0 ga enc

instance PrettyPrint G_mapping where
    printText0 ga (G_symb_map gsmil) = printText0 ga gsmil
    printText0 ga (G_logic_translation enc) =
        printLogicEncoding ga enc

instance PrettyPrint G_hiding where
    printText0 ga (G_symb_list gsil) = printText0 ga gsil
    printText0 ga (G_logic_projection enc) =
        printLogicEncoding ga enc

instance PrettyPrint GENERICITY where
    printText0 ga (Genericity aa ab _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
        in hang aa' 6 ab'

instance PrettyPrint PARAMS where
    printText0 ga (Params aa) =
        if null aa then empty
        else sep $ map (brackets.(nest (-4)).(printText0 ga)) aa

instance PrettyPrint IMPORTED where
    printText0 ga (Imported aa) =
        if null aa then empty
        else text givenS <+> (fsep $ punctuate comma $
                                         map (printGroupSpec ga) aa)

instance PrettyPrint FIT_ARG where
    printText0 ga (Fit_spec aa ab _) =
        let aa' = printText0 ga aa
            ab' = fcat $ map (printText0 ga) ab
        in aa' <> (if null ab then empty else space <> hang (text fitS) 4 ab')
    printText0 ga (Fit_view aa ab _) =
        let aa' = printText0 ga aa
            ab' = print_fit_arg_list printText0 sp_brackets sep ga ab
        in hang (text viewS <+> aa') 4 ab'

instance PrettyPrint Logic_code where
    printText0 ga (Logic_code (Just enc) (Just src) (Just tar) _) =
        printText0 ga enc <+> colon <+>
        printText0 ga src <+> funD <+>
        printText0 ga tar
    printText0 ga (Logic_code (Just enc) (Just src) Nothing _) =
        printText0 ga enc <+> colon <+>
        printText0 ga src <+> funD
    printText0 ga (Logic_code (Just enc) Nothing (Just tar) _) =
        printText0 ga enc <+> colon <+>
        funD <+> printText0 ga tar
    printText0 ga (Logic_code Nothing (Just src) (Just tar) _) =
        printText0 ga src <+> funD <+>
        printText0 ga tar
    printText0 ga (Logic_code (Just enc) Nothing Nothing _) =
        printText0 ga enc
    printText0 ga (Logic_code Nothing (Just src) Nothing _) =
        printText0 ga src <+> funD
    printText0 ga (Logic_code Nothing Nothing (Just tar) _) =
        funD <+> printText0 ga tar
    printText0 _ (Logic_code Nothing Nothing Nothing _) =
        error "PrettyPrint Logic_code"

funD :: Doc
funD = text funS

instance PrettyPrint Logic_name where
    printText0 ga (Logic_name mlog slog) =
        printText0 ga mlog <>
                       (case slog of
                       Nothing -> empty
                       Just sub -> char '.' <> printText0 ga sub)

-----------------------------------------------
{- |
  specealized printing of 'FIT_ARG's
-}
print_fit_arg_list :: (GlobalAnnos -> (Annoted FIT_ARG) -> Doc)
                   -> (Doc -> Doc) -- ^ a function enclosing the Doc
                                   -- in brackets
                   -> ([Doc] -> Doc) -- ^ a function printing a list
                                     -- of Doc seperated by space
                   -> GlobalAnnos -> [Annoted FIT_ARG] -> Doc
print_fit_arg_list _pf _b_fun _sep_fun _ga [] = empty
print_fit_arg_list pf b_fun _sep_fun ga [fa] = b_fun $ pf ga fa
print_fit_arg_list pf b_fun sep_fun ga fas =
    sep_fun $ map (b_fun . (pf ga)) fas
{- |
   conditional generation of grouping braces for Union and Extension
-}
condBracesGroupSpec :: (GlobalAnnos -> (Annoted SPEC) -> Doc)
                    -> (Doc -> Doc) -- ^ a function enclosing the Doc
                                    -- in braces
                    -> Maybe (String,Doc) -- ^ something like a keyword
                                          -- that should be right before
                                          -- the braces
                    -> GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesGroupSpec pf b_fun mkeyw ga as =
    case skip_Group $ item as of
                 Spec_inst _ _ _ -> str_doc'<>as'
                 Union _ _       -> nested''
                 Extension _ _   -> nested''
                 _               ->
                     str_doc'<>b_fun as'
    where as' = pf ga as

          (_str,str_doc) = maybe ("",empty) id mkeyw
          str_doc' = if isEmpty str_doc then empty
                     else str_doc
          nested'' = str_doc' <>b_fun as'

{- |
  generate grouping braces for Tanslations and Reductions
-}
condBracesTransReduct :: (GlobalAnnos -> (Annoted SPEC) -> Doc)
                      -> (Doc -> Doc) -- ^ a function enclosing the Doc
                                      -- in brackets
                      -> GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesTransReduct pf b_fun ga as =
    case skip_Group $ item as of
                 Extension _ _    -> nested''
                 Union _ _        -> nested''
                 Local_spec _ _ _ -> nested''
                 _                -> as'
    where as' = pf ga as
          nested'' = b_fun as'

{- |
  generate grouping braces for Within
-}
condBracesWithin :: (GlobalAnnos -> (Annoted SPEC) -> Doc)
                 -> (Doc -> Doc) -- ^ a function enclosing the Doc
                                 -- in braces
                 -> GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesWithin pf b_fun ga as =
    case skip_Group $ item as of
                 Extension _ _    -> nested''
                 Union _ _        -> nested''
                 _                -> as'
    where as' = pf ga as
          nested'' = b_fun as'
{- |
  only Extensions inside of Unions (and) need grouping braces
-}
condBracesAnd :: (GlobalAnnos -> (Annoted SPEC) -> Doc)
              -> (Doc -> Doc) -- ^ a function enclosing the Doc
                              -- in braces
              -> GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesAnd pf b_fun ga as =
    case skip_Group $ item as of
                 Extension _ _    -> nested''
                 _                -> as'
    where as' = pf ga as
          nested'' = b_fun as'

skip_Group :: SPEC -> SPEC
skip_Group sp =
    case sp of
            Group as _ -> skip_Group $ item as
            _          -> sp

-- ToDo: \\THENIMPLIES,... erzeugen
--       Dazu Hilfsfunktionen erzeugen
--       nachschauen wie implies zur Zeit gesetzt wird
--
-- |
-- prints the keyword or spec head with following semantic annotation
-- if any and the list of non sematic annotations if any and
-- then the following item from 'Annoted' a
spAnnotedPrint :: (a -> Doc) -- ^ print function for the item
               -> (Annotation -> Doc) -- ^ print function for the annotation
               -> (Doc -> Doc -> Doc) -- ^ a function like '<+>'
               -> Doc -- ^ keyword or spec head (spec ... =)
               -> Annoted a -- ^ item to print after keyword or spec head
               -> Doc
spAnnotedPrint pf pAn beside_ keyw ai =
    case ai of
         Annoted i _ las _ ->
          let i'           = pf i
              (msa,as)     = case las of
                                []     -> (Nothing,[])
                                (x:xs) | isSemanticAnno x -> (Just x,xs)
                                xs     -> (Nothing,xs)
              (san,anno)   = case msa of
                               Nothing -> (empty, empty)
                               Just a  -> (pAn a, checkAnno a keyw beside_
                                                   $ pAn a)
              as'          = if null as then empty else vcat $ map pAn as
                         -- Todo: indent annos
          in  case (render keyw) of
                "\\THEN" | not $ isEmpty anno  -> anno $+$ as' $+$ i'
                _keyw'                         -> keyw `beside_` san $+$ as'
                                                  $+$ i'
    where checkAnno an _keyword _beside san' =
            case an of
                 Semantic_anno anno _ ->
                          case anno of
                                SA_cons     -> sp_text 0 "\\THENCONS"
                                SA_def      -> sp_text 0 "\\THENDEF"
                                SA_implies  -> sp_text 0 "\\THENIMPLIES"
                                SA_mono     -> sp_text 0 "\\THENMONO"
                                _anno'      -> keyw `beside_` san'
                 _an' -> keyw `beside_` san'
