{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Printer for N-triples

-}

module RDF.Print where

import OWL2.AS
import OWL2.Print ()
import Common.AS_Annotation
import Common.Doc
import Common.DocUtils

import RDF.AS
import RDF.Symbols
import RDF.Sign

import qualified Data.Set as Set

-- | RDF signature printing

printRDFBasicTheory :: (Sign, [Named Axiom]) -> Doc
printRDFBasicTheory (_, l) = vsep (map (pretty . sentence) l)

instance Pretty Sign where
    pretty = printSign
    
printNodes :: String -> Set.Set IRI -> Doc
printNodes s iris = text "#" <+> text s $+$ (vcat $ map (text "#\t\t" <+>) $ map pretty $ Set.toList iris)

printSign :: Sign -> Doc
printSign s = text "#" $+$ printNodes "subjects:" (subjects s)
    $+$ printNodes "predicates:" (predicates s)
    $+$ printNodes "objects:" (objects s)
    $+$ text "#"

instance Pretty Axiom where
    pretty = printAxiom

printAxiom :: Axiom -> Doc
printAxiom (Axiom sub pre obj)
    = pretty sub <+> pretty pre <+> printObject obj <+> text "."

printObject :: Object -> Doc
printObject obj = case obj of
    Left iri -> pretty iri
    Right lit -> pretty lit

instance Pretty RDFGraph where
    pretty = printGraph

printGraph :: RDFGraph -> Doc
printGraph (RDFGraph sl) = vcat $ map pretty sl

instance Pretty SymbItems where
instance Pretty SymbMapItems where
instance Pretty RDFEntity where
instance Pretty RawSymb where


