{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This module contains all instances of PrettyPrint for AS_Annotation.hs
-}

module Common.Print_AS_Annotation where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Id
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Lexer(whiteChars)

instance PrettyPrint Annotation where
    printText0 _ (Unparsed_anno aw at _) =
        case at of 
                Line_anno str -> 
                    (case aw of 
                            Comment_start -> ptext "%%"
                            Annote_word w ->  ptext $ "%" ++ w) 
                    <> (if all (`elem` whiteChars) str 
                        then empty else ptext str)
                Group_anno strs -> 
                    let docs = map ptext strs
                        (o, c) = case aw of 
                            Comment_start -> (ptext "%{",  ptext "}%")
                            Annote_word w -> (ptext ("%" ++ w ++ "("), 
                                              ptext ")%")
                        in case docs of 
                           [] -> empty
                           [h] ->  o <> h <> c
                           h : t -> vcat ((o <> h) : init t ++ [last t <> c])
    printText0 ga (Display_anno aa ab _) =
        let aa' = printText0 ga aa
            ab' = fcat $ punctuate space $ map printPair $ filter nullSnd ab
        in printGroup (ptext "display") $ aa' <+> ab'
           where printPair (s1,s2) = ptext ("%" ++ lookupDisplayFormat s1) 
                                     <+> ptext s2
                 nullSnd (_,s2) = not $ null s2
    printText0 ga (String_anno aa ab _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
        in printLine (ptext "string") $ aa' <> comma <+> ab'
    printText0 ga (List_anno aa ab ac _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
            ac' = printText0 ga ac
        in printLine (ptext "list") $ aa' <> comma <+> ab' <> comma <+> ac'
    printText0 ga (Number_anno aa _) =
        let aa' = printText0 ga aa
        in printLine (ptext "number") aa'
    printText0 ga (Float_anno aa ab _) =
        let aa' = printText0 ga aa
            ab' = printText0 ga ab
        in printLine (ptext "floating") $ aa' <> comma <+> ab'
    printText0 ga (Prec_anno pflag ab ac _) =
        let aa' = ptext $ showPrecRel pflag
            ab' = fcat $ punctuate (comma <> space) $ map (printText0 ga) ab
            ac' = fcat $ punctuate (comma <> space) $ map (printText0 ga) ac
        in  printGroup (ptext "prec") $ braces ab' <+> aa' <+> braces ac'
    printText0 ga (Assoc_anno as aa _) =
        printGroup (case as of ARight -> ptext "right_assoc"
                               ALeft -> ptext "left_assoc") $ fcat $ 
                                punctuate (comma <> space) $ 
                                          map (printText0 ga) aa
    printText0 _ (Label [] _) = empty
    printText0 _ (Label aa _) =
        let aa' = vcat $ map ptext aa
        in ptext "%(" <> aa' <> ptext ")%"
    printText0 _ (Semantic_anno sa _) =
        printLine (ptext $ lookupSemanticAnno sa) empty
-- -------------------------------------------------------------------------
-- utilies
-- -------------------------------------------------------------------------
showPrecRel :: PrecRel -> String
showPrecRel p = case p of Lower -> "<"
                          Higher -> ">"
                          BothDirections -> "<>"
                          NoDirection -> error "showPrecRel"

printCommaIds :: GlobalAnnos -> [Id] -> Doc
printCommaIds ga = fcat . punctuate (comma <> space) . map (printText0 ga)

printGroup :: Doc -> Doc -> Doc
printGroup key grp = ptext "%" <> key <> ptext "(" <> grp <> ptext ")%"

printLine :: Doc -> Doc -> Doc
printLine key line = if isEmpty line then pkey else pkey <+> line
    where pkey = ptext "%" <> key

printAnnotationList_Text0 :: GlobalAnnos -> [Annotation] -> Doc
printAnnotationList_Text0 ga l = (vcat $ map (printText0 ga) l) 

instance (PrettyPrint a) => PrettyPrint (Annoted a) where
    printText0 ga (Annoted i _ las ras) =
        let i'   = printText0 ga i
            las' = printAnnotationList_Text0 ga las
            (la,rras) = case ras of
                        []     -> (empty,[])
                        r@(l:xs)
                            | isLabel l -> (printText0 ga l,xs)
                            | otherwise -> (empty,r)
            ras' = printAnnotationList_Text0 ga rras
        in las' $+$ (hang i' 0 la) $$ ras'

instance PrettyPrint s => PrettyPrint (Named s) where
    printText0 ga = printText0 ga . sentence
-- other stuff must be printed logic dependent 

-- | print sentence with label and non-axioms with implied annotation 
printLabelledSen :: PrettyPrint s => GlobalAnnos -> Named s -> Doc
printLabelledSen ga s@NamedSen{senName = label, isAxiom = isAx} =  
    printText0 ga s <> (if null label then empty else
           space <> printText0 ga (Label [label] nullRange))
        <> if isAx then empty else
        space <> printText0 ga (Semantic_anno SA_implied nullRange)

-- | function to split the annotation to the right of an item
-- * fst contains printed label and implied annotion 
--   if any at the begining of the list of annotations
-- * snd contains the remaining annos
splitAndPrintRAnnos :: (GlobalAnnos -> Annotation -> d)
                       -> (GlobalAnnos -> [Annotation] -> d)
                       -> (d -> d -> d)    -- ^ a beside with space 
                                                 -- like <+> or <\+>
                       -> (d -> d) -- ^ for Latex something to move the label 
                              -- and \/ or implied annotation to the right 
                              -- margin
                       -> d   -- ^ empty doc
                       -> GlobalAnnos -> [Annotation] -> (d, d)
splitAndPrintRAnnos pf pf_list sepF move nil ga ras =
    case ras of
             []     -> (nil,nil)
             r@(l:[])
                 | isLabel l -> (pf ga l,nil)
                 | isImplied l -> (move $ pf ga l, nil)
                 | otherwise -> (nil,pf_list ga r)
             r@(l:impl:xs)
                 | isLabel l && not (isImplied impl) 
                     -> (pf ga l, pf_list ga (impl:xs))
                 | isLabel l && isImplied impl 
                     -> (pf ga l `sepF` pf ga impl, pf_list ga xs)
                 | isImplied l 
                     -> (move $ pf ga l, pf_list ga (impl:xs))
                 | otherwise -> (nil,pf_list ga r)
