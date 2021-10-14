module OWL2.Pretty where

import OWL2.AS

import OWL2.Sign (emptySign)

import Common.Doc(Doc)
import Common.DocUtils

import qualified OWL2.PrintAS as PAS
import qualified OWL2.PrintMS as PMS
import qualified OWL2.XMLConversion as PXML

import Text.XML.Light.Output (ppElement)
import Common.Doc (text)

instance Pretty OntologyDocument where
    pretty o@(OntologyDocument m _ _) = case syntaxType m of
        AS -> PAS.printOntologyDocument o
        MS -> PMS.printOntologyDocument o
        XML -> text $ ppElement $ PXML.xmlOntologyDoc emptySign o

instance Pretty Axiom where
    pretty = PAS.printAxiom mempty

toDocAsXML :: OntologyDocument -> Doc
toDocAsXML = pretty . changeSyntax XML

toDocAsAS :: OntologyDocument -> Doc
toDocAsAS = pretty . changeSyntax AS

toDocAsMS :: OntologyDocument -> Doc
toDocAsMS = pretty . changeSyntax MS