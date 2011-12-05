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

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords

import OWL2.AS
import OWL2.Print
import RDF.AS
import RDF.Parse
import RDF.Symbols

instance Pretty Sentence where
    pretty = printSentence

printSentence :: Sentence -> Doc
printSentence (Sentence sub pre obj)
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


