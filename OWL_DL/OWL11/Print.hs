{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for URIreference and Namespace)

Pretty printing for OWL DL theories.
-}

module OWL_DL.OWL11.Print where

import Common.Doc
import Common.DocUtils

import OWL_DL.OWL11.Sign
import OWL_DL.OWL11.FFS

import qualified Data.Set as Set
import qualified Data.Map as Map

instance Pretty Sign where
    pretty = text .  show    -- printSign

printSign :: Sign -> Doc
printSign (Sign _ p2 p3 p4 p5 p6 _ p8 p9 p10) =
    text "namespaces " $+$ printNamespace p10 $+$
    text "concepts" <+> setToDocF p2 $+$
    text "primaryConcepts " <+> setToDocF p3 $+$
    text "datatypes " <+> setToDocF p4 $+$
    text "indvidual_valued_roles " <+> setToDocF p5 $+$
    text "data_valued_roles " <+> setToDocF p6 $+$
    text "individuals " <+> setToDocF p8 $+$
    text "sign_axioms" $+$ vcat (setToDocs p9)

instance Pretty URIreference where
    pretty = printURIreference

printURIreference :: URIreference -> Doc
printURIreference (QN prefix localpart u)
    | localpart == "_" = text $ show "_"
    | null prefix = if null u then
                           text localpart
                           else text $ show (u ++ ":" ++ localpart)
    | otherwise =   text $ show ( prefix ++ ":" ++ localpart)

printNamespace :: Namespace -> Doc
printNamespace nsMap =
    vcat $ map pp (Map.toList nsMap)
       where pp :: (String, String) -> Doc
             pp (s1,s2) = text s1 <> defn <> text s2

instance Pretty Sentence where
    pretty = text . show -- printSentence


-- not necessary
instance Pretty OntologyFile where
    pretty = text . show
instance Pretty Ontology where
    pretty = text . show  -- printOntology

instance Pretty Axiom where
    pretty = text . show   -- printAxiom


instance Pretty SignAxiom where
    pretty = text . show -- printSignAxiom


setToDocs :: Pretty a => Set.Set a -> [Doc]
setToDocs = punctuate comma . map pretty . Set.toList

setToDocF :: Pretty a => Set.Set a -> Doc
setToDocF = fsep . setToDocs

setToDocV :: (Pretty a) => Set.Set a -> Doc
setToDocV = vcat . setToDocs

-- output a list in vertikal direction
listToDocV :: (Pretty a, Pretty b)
                  => (a -> b -> Doc) -> a -> [b] -> Doc
listToDocV printForm iD = vcat . map (printForm iD)

-- output a list in horizonal direction
listToDocH :: (Pretty a, Pretty b)
                  =>  (a -> b -> Doc) -> a -> [b] -> Doc
listToDocH printForm iD = hsep . map (printForm iD)


emptyQN :: QName
emptyQN = QN "" "" ""

simpleQN :: String -> QName
simpleQN str = QN "" str ""

choiceName :: Int -> String
choiceName level
    | level <= 0 = "x"
    | level == 1 = "y"
    | level == 2 = "z"
    | otherwise = "u" ++ (show (level -2))
