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

import Common.Id
import Common.Doc
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Pretty as Pretty
import Common.GlobalAnnotations

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
