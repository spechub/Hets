module OWL2.Pretty where

import OWL2.AS

import Common.DocUtils

import qualified OWL2.PrintAS as PAS
import qualified OWL2.PrintMS as PMS

instance Pretty OntologyDocument where
    pretty o@(OntologyDocument m _ _) = case syntaxType m of
        AS -> PAS.printOntologyDocument o
        MS -> PMS.printOntologyDocument o