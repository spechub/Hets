{- |
Module      :  $Header$
Copyright   :  Felix Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

analyse OWL files by calling the external Java parser.
-}

module RDF.ParseRDFAsLibDefn (parseRDF) where

import RDF.AS
import RDF.Parse
import RDF.Logic_RDF

import Common.Id
import Common.LibName
import Common.AS_Annotation hiding (isAxiom, isDef)

import Logic.Grothendieck

import Driver.Options

import Syntax.AS_Library
import Syntax.AS_Structured

import System.Directory
import System.Exit
import System.Process

parseRDF :: FilePath              -- ^ local filepath or uri
         -> IO LIB_DEFN        -- ^ map: uri -> RDF graph
parseRDF filename = do
    absfile <- if checkUri filename then return filename else
      canonicalizePath filename
    let absfileNt = absfile ++ ".nt"
    ec <- system $ "cwm --rdf " ++ absfile ++ " --ntriples > " ++ absfileNt ++ " 2> /dev/null"
    case ec of
        ExitSuccess -> parseNT absfileNt
        _ -> parseNT absfile

parseNT :: FilePath -> IO LIB_DEFN
parseNT filename = fmap (convertToLibDefN filename) $ parseNtriples filename

createSpec :: RDFGraph -> Annoted SPEC
createSpec gr = emptyAnno $ Basic_spec (G_basic_spec RDF gr) nullRange

convertone :: RDFGraph -> Annoted LIB_ITEM
convertone gr = emptyAnno $ Spec_defn (mkSimpleId "") emptyGenericity (createSpec gr) nullRange

convertToLibDefN :: FilePath -> RDFGraph -> LIB_DEFN
convertToLibDefN filename l = Lib_defn
  (emptyLibName $ convertFileToLibStr filename)
  [convertone l] nullRange []
