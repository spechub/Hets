module OWL2.Pretty where

import OWL2.AS


import Common.Doc(Doc)
import Common.DocUtils

import qualified OWL2.PrintAS as PAS
import qualified OWL2.PrintMS as PMS

instance Pretty OntologyDocument where
    pretty o@(OntologyDocument m _ _) = case syntaxType m of
        AS -> PAS.printOntologyDocument o
        MS -> PMS.printOntologyDocument o

instance Pretty Axiom where
    pretty = PAS.printAxiom mempty

toDocAsXML :: OntologyDocument -> Doc
toDocAsXML = pretty . changeSyntax XML

toDocAsAS :: OntologyDocument -> Doc
toDocAsAS = pretty . changeSyntax AS

toDocAsMS :: OntologyDocument -> Doc
toDocAsMS = pretty . changeSyntax MS