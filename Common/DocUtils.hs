{- |
Module      :  ./Common/DocUtils.hs
Description :  Pretty class for pretty printing with instances plus utilities
Copyright   :  (c) jianchun wang and Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

'Pretty' class for pretty printing, some instances and other utility functions
-}

module Common.DocUtils where

import Common.AS_Annotation
import Common.Doc
import Common.Id
import Common.IRI
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map
import Common.GlobalAnnotations
import Data.Hashable

-- * the class stuff
class Show a => Pretty a where
    pretty :: a -> Doc
    pretties :: [a] -> Doc
    pretties = brackets . ppWithCommas

instance Pretty Char where
    pretty c = text [c]
    pretties = text . take 25

instance Pretty () where
    pretty () = empty

instance Pretty Id where
    pretty = idDoc

instance Pretty Annotation where
    pretty = annoDoc

instance Pretty Token where
   pretty = sidDoc

-- | convert a token to a document (different from 'text' for LaTex)
sidDoc :: Token -> Doc
sidDoc = idDoc . simpleIdToId

-- | print several annotations vertically (each in a new line)
printAnnotationList :: [Annotation] -> Doc
printAnnotationList = vcat . map annoDoc

-- | print annotations flush right
printTrailer :: [Annotation] -> Doc
printTrailer = flushRight . hsep . map annoDoc

-- | add trailing annotation to a document
splitAndPrintRAnnos :: Doc -> [Annotation] -> Doc
splitAndPrintRAnnos i ras =
    let (r, s) = splitRAnnos ras
    in (if null s then id else ($+$ printAnnotationList s))
       $ if null r then i else fsep [i, printTrailer r]

-- | conditionally add a 'semi' after the doc but before trailing annotations
printSemiAnno :: (a -> Doc) -> Bool -> Annoted a -> Doc
printSemiAnno pp addSemi (Annoted i _ las ras) =
    let r = splitAndPrintRAnnos
            ((if addSemi then (<> semi) else id) $ pp i) ras
    in if null las then r else
           (if startsWithSemanticAnno las then id else (text "" $+$))
              $ printAnnotationList las $+$ r

-- | test for semantic annos before structured specs
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
fromLabelledSen s = let label = senAttr s in
    appendAnno (emptyAnno $ sentence s) $
    (if null label then [] else [Label [label] nullRange])
    ++ if isAxiom s then [] else [Semantic_anno SA_implied nullRange]

{- | function to split the annotation to the right of an item.
* fst contains printed label and implied annotion
  if any at the begining of the list of annotations
* snd contains the remaining annos -}
splitRAnnos :: [Annotation] -> ([Annotation], [Annotation])
splitRAnnos r = case r of
    [l] | isLabel l || isImplied l -> (r, [])
    l : s@(i : t)
      | isLabel l ->
            if isImplied i then ([l, i], t)
            else ([l], s)
      | isImplied l -> ([l], s)
    _ -> ([], r)

-- | add global annotations for proper mixfix printing
useGlobalAnnos :: GlobalAnnos -> Doc -> Doc
useGlobalAnnos = changeGlobalAnnos . const

-- | like punctuate but prepends the symbol to all tail elements
prepPunctuate :: Doc -> [Doc] -> [Doc]
prepPunctuate s l = case l of
    x : r@(_ : _) -> x : map (s <>) r
    _ -> l

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

ppWithCommas :: Pretty a => [a] -> Doc
ppWithCommas = sepByCommas . map pretty

instance (Pretty a, Pretty b) => Pretty (a, b) where
    pretty = printPair pretty pretty

printPair :: (a -> Doc) -> (b -> Doc) -> (a, b) -> Doc
printPair fA fB (a, b) = parens $ sepByCommas [fA a, fB b]

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
    pretty = printTriple pretty pretty pretty

printTriple :: (a -> Doc) -> (b -> Doc) -> (c -> Doc) -> (a, b, c) -> Doc
printTriple fA fB fC (a, b, c) = parens $ sepByCommas [fA a, fB b, fC c]

instance (Pretty a, Pretty b, Pretty c, Pretty d) => Pretty (a, b, c, d) where
    pretty (a, b, c, d) =
      parens $ sepByCommas [pretty a, pretty b, pretty c, pretty d]

instance Pretty Int where
    pretty = sidDoc . mkSimpleId . show

instance Pretty Integer where
    pretty = sidDoc . mkSimpleId . show

instance Pretty a => Pretty [a] where
    pretty = pretties

instance Pretty a => Pretty (Set.HashSet a) where
    pretty = printSet braces sepByCommas

-- | container size
data CSize = CEmpty | CSingle | CMult

ppList :: (a -> Doc) -> (CSize -> Doc -> Doc) -> ([Doc] -> Doc) -> [a] -> Doc
ppList fa brace inter l = case l of
  [] -> brace CEmpty empty
  [e] -> brace CSingle $ fa e
  _ -> brace CMult . inter $ map fa l

ppSet :: (a -> Doc) -> (CSize -> Doc -> Doc) -> ([Doc] -> Doc)
  -> Set.HashSet a -> Doc
ppSet fa brace inter = ppList fa brace inter . Set.toList

optBraces :: CSize -> Doc -> Doc
optBraces c = case c of
  CSingle -> id
  _ -> braces

printSet :: Pretty a => (Doc -> Doc) -> ([Doc] -> Doc) -> Set.HashSet a -> Doc
printSet = ppSet pretty . const

printSetMap :: (Pretty k, Pretty a, Hashable k) => Doc -> Doc -> Map.HashMap k (Set.HashSet a)
  -> Doc
printSetMap header sepa = vcat . concatMap ( \ (i, s) ->
    map ( \ e -> header <+> pretty i <+> colon <> sepa <> pretty e)
            $ Set.toList s) . Map.toList

printMap :: (Pretty a, Pretty b, Hashable a) => (Doc -> Doc) -> ([Doc] -> Doc)
         -> (Doc -> Doc -> Doc) -> Map.HashMap a b -> Doc
printMap = ppMap pretty pretty . const

ppMap :: (Hashable a) => (a -> Doc) -> (b -> Doc) -> (CSize -> Doc -> Doc) -> ([Doc] -> Doc)
      -> (Doc -> Doc -> Doc) -> Map.HashMap a b -> Doc
ppMap fa fb brace inter pairDoc =
    ppPairlist fa fb brace inter pairDoc . Map.toList

ppPairlist :: (a -> Doc) -> (b -> Doc) -> (CSize -> Doc -> Doc)
  -> ([Doc] -> Doc) -> (Doc -> Doc -> Doc) -> [(a, b)] -> Doc
ppPairlist fa fb brace inter pairDoc =
  ppList (\ (a, b) -> pairDoc (fa a) (fb b)) brace inter

pairElems :: Doc -> Doc -> Doc
pairElems a b = a <+> mapsto <+> b

instance (Pretty a, Pretty b, Hashable a) => Pretty (Map.HashMap a b) where
    pretty = printMap braces sepByCommas pairElems

-- | start with a bullet, i.e. formulas
addBullet :: Doc -> Doc
addBullet = (bullet <+>)

showDoc :: Pretty a => a -> ShowS
showDoc = shows . pretty

-- | like showDoc but considers global annotations
showGlobalDoc :: Pretty a => GlobalAnnos -> a -> ShowS
showGlobalDoc ga = shows . useGlobalAnnos ga . pretty

instance Pretty IRI where
  pretty = text . show
