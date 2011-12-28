{- |
Module      :  $Header$
Copyright   :  Felix Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

analyse RDF files by calling the cwm tool
<http://www.w3.org/2000/10/swap/doc/cwm.html>
-}

module RDF.ParseRDFAsLibDefn (parseRDF) where

import Common.Id
import Common.LibName
import Common.AS_Annotation hiding (isAxiom, isDef)

import Logic.Grothendieck

import RDF.AS
import RDF.Parse
import RDF.Logic_RDF

import Syntax.AS_Library
import Syntax.AS_Structured

import System.Exit
import System.Process

{-- | top-level function for parsing RDF; it first tries to parse RDF-XML and
if this fails, it tries to parse ntriples --}
parseRDF :: FilePath                -- ^ local filepath or uri
         -> IO LIB_DEFN             -- ^ map: uri -> RDF graph
parseRDF filename = do
    let triplesFile = filename ++ ".nt"
    ec <- system $ "cwm --rdf " ++ filename
        ++ " --ntriples > " ++ triplesFile ++ " 2> /dev/null"
    case ec of
        ExitSuccess -> parseNTriplesToLibDefn triplesFile
        _ -> parseNTriplesToLibDefn filename

parseNTriplesToLibDefn :: FilePath -> IO LIB_DEFN
parseNTriplesToLibDefn filename = fmap (convertToLibDefN filename)
    $ parseNTriplesFile filename

createSpec :: RDFGraph -> Annoted SPEC
createSpec gr = emptyAnno $ Basic_spec (G_basic_spec RDF gr) nullRange

convertone :: RDFGraph -> Annoted LIB_ITEM
convertone gr = emptyAnno $ Spec_defn (mkSimpleId "")
    emptyGenericity (createSpec gr) nullRange

convertToLibDefN :: FilePath -> RDFGraph -> LIB_DEFN
convertToLibDefN filename l = Lib_defn
  (emptyLibName $ convertFileToLibStr filename) [convertone l] nullRange []
