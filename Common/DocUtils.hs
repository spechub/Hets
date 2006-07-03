{- |
Module      :  $Header$
Copyright   :  (c) jianchun wang and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  wjch868@tzi.de
Stability   :  provisional
Portability :  portable

some instances for the class Pretty
-}

module Common.DocUtils where

import Common.AS_Annotation
import Common.Doc
import Common.Id
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Pretty as Pretty
import Common.GlobalAnnotations

-- * the class stuff
class Show a => Pretty a where
    pretty :: a -> Doc

instance Pretty () where
    pretty () = empty

instance Pretty Id where
    pretty = idDoc

instance Pretty Annotation where
    pretty = annoDoc

instance Pretty Token where
   pretty = sidDoc

sidDoc :: Token -> Doc
sidDoc = idDoc . simpleIdToId

-- | print several annotations vertically (each in a new line)
printAnnotationList :: [Annotation] -> Doc
printAnnotationList = vcat . map annoDoc

printTrailer :: [Annotation] -> Doc
printTrailer = flushRight . hsep . map annoDoc

-- | add trailing annotation to a document
splitAndPrintRAnnos :: Doc -> [Annotation] -> Doc
splitAndPrintRAnnos i ras =
    let (r, s) = splitRAnnos ras
    in (if null s then id else ($+$ printAnnotationList s))
       $ if null r then i else fsep [i, printTrailer r]

printSemiAnno :: (a -> Doc) -> Bool -> Annoted a -> Doc
printSemiAnno pp addSemi (Annoted i _ las ras) =
    let r = splitAndPrintRAnnos
            ((if addSemi then (<> semi) else id) $ pp i) ras
    in if null las then r else
           (if startsWithSemanticAnno las then id else (text "" $+$))
              $ printAnnotationList las $+$ r

startsWithSemanticAnno :: [Annotation] -> Bool
startsWithSemanticAnno l = case l of
    Semantic_anno _ _ : _ -> True
    _ -> False

-- | print annoted items with trailing semicolons except for the last item
semiAnnos :: (a -> Doc) -> [Annoted a] -> Doc
semiAnnos pp l = if null l then empty else
           vcat $ map (printSemiAnno pp True) (init l)
                ++ [printAnnoted pp $ last l]

-- | print sentence with label and non-axioms with implied annotation
printAnnoted :: (a -> Doc) -> Annoted a -> Doc
printAnnoted pp = printSemiAnno pp False

instance (Pretty a) => Pretty (Annoted a) where
    pretty = printAnnoted pretty

-- | convert a named sentence into an annoted one
fromLabelledSen :: Named s -> Annoted s
fromLabelledSen s = let label = senName s in
    appendAnno (emptyAnno $ sentence s) $
    (if null label then [] else [Label [label] nullRange])
    ++ if isAxiom s then [] else [Semantic_anno SA_implied nullRange]

instance Pretty s => Pretty (Named s) where
    pretty = pretty . fromLabelledSen

-- | function to split the annotation to the right of an item
-- * fst contains printed label and implied annotion
--   if any at the begining of the list of annotations
-- * snd contains the remaining annos
splitRAnnos :: [Annotation] -> ([Annotation], [Annotation])
splitRAnnos r = case r of
    [] -> ([],[])
    [l] -> if isLabel l || isImplied l then (r, [])
             else ([], r)
    l : s@(i : t) ->
        if isLabel l then
            if isImplied i then ([l, i], t)
            else ([l], s)
        else if isImplied l then ([l], s)
             else ([], r)

-- | add global annotations for proper mixfix printing
useGlobalAnnos :: GlobalAnnos -> Doc -> Doc
useGlobalAnnos ga = changeGlobalAnnos (const ga)

-- | like punctuate but prepends the symbol to all tail elements
prepPunctuate :: Doc -> [Doc] -> [Doc]
prepPunctuate s l = case l of
    x : r@(_ : _) -> x : map (s <>) r
    _ -> l

toOldText :: Pretty a => GlobalAnnos -> a -> Pretty.Doc
toOldText ga = toText ga . pretty

toOldLatex :: Pretty a => GlobalAnnos -> a -> Pretty.Doc
toOldLatex ga = toLatex ga . pretty

instance (Pretty a, Pretty b) => Pretty (Either a b) where
    pretty = printEither pretty pretty

printEither :: (a -> Doc) -> (b -> Doc) -> Either a b -> Doc
printEither fA fB ei = case ei of
    Left x -> fA x
    Right x -> fB x

instance Pretty a => Pretty (Maybe a) where
    pretty = printMaybe pretty

printMaybe :: (a -> Doc) -> Maybe a -> Doc
printMaybe fA mb = case mb of
    Just x -> fA x
    Nothing -> empty

instance (Pretty a, Pretty b) => Pretty (a, b) where
    pretty = printPair pretty pretty

printPair :: (a -> Doc) -> (b -> Doc) -> (a, b) -> Doc
printPair fA fB (a, b) =
    lparen <> fA a <> comma <> fB b <> rparen

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
    pretty = printTriple pretty pretty pretty

printTriple :: (a -> Doc) -> (b -> Doc) -> (c -> Doc) -> (a, b, c) -> Doc
printTriple fA fB fC (a,b,c) =
    lparen <> fA a <> comma <> fB b <> comma <> fC c <> rparen

instance Pretty Int where
    pretty = text . show

printSetWithComma :: Pretty a => Set.Set a -> Doc
printSetWithComma = printSet id (fsep . punctuate comma)

printList :: (Doc -> Doc) -> ([Doc] -> Doc) -> [Doc] -> Doc
printList brace inter = brace . inter

instance Pretty a => Pretty [a] where
    pretty = printList brackets (fsep . punctuate comma) . map pretty

printSet :: Pretty a => (Doc -> Doc) -> ([Doc] -> Doc) -> Set.Set a -> Doc
printSet brace inter = printList brace inter . map pretty . Set.toList

instance Pretty a => Pretty (Set.Set a) where
    pretty = printSet specBraces (fsep . punctuate comma)

printMap :: (Pretty a, Ord a, Pretty b) => (Doc -> Doc) -> ([Doc] -> Doc)
         -> (Doc -> Doc -> Doc) -> Map.Map a b -> Doc
printMap brace inter pairDoc = printList brace inter
     . map ( \ (a, b) -> pairDoc (pretty a) (pretty b))
     . Map.toList

instance (Ord a, Pretty a, Pretty b) => Pretty (Map.Map a b) where
    pretty = printMap specBraces (fsep . punctuate comma)
             (\ a b -> a <+> mapsto <+> b)

addBullet :: Doc -> Doc
addBullet = (bullet <+>)

showDoc :: Pretty a => a -> ShowS
showDoc = shows . pretty

showGlobalDoc :: Pretty a => GlobalAnnos -> a -> ShowS
showGlobalDoc ga = shows . toOldText ga
