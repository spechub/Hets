{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

analyse OWL files by calling the external Java parser.
-}

module OWL2.ParseOWLAsLibDefn (parseOWL) where

import OWL2.AS
import OWL2.MS
import OWL2.Rename

import Data.Char
import qualified Data.Map as Map

import Common.Id
import Common.IRI (simpleIdToIRI)
import Common.LibName
import Common.ProverTools
import Common.AS_Annotation hiding (isAxiom, isDef)
import Common.Utils (executeProcess)

import Logic.Grothendieck
import OWL2.Logic_OWL2
import OWL2.XML

import Driver.Options

import Syntax.AS_Library
import Syntax.AS_Structured

import System.Directory
import System.Exit
import System.FilePath

import Text.XML.Light
  (parseXML, onlyElems, filterElementsName, findAttr, unqual)

-- | call for owl parser (env. variable $HETS_OWL_TOOLS muss be defined)
parseOWL :: FilePath              -- ^ local filepath or uri
         -> IO LIB_DEFN        -- ^ map: uri -> OntologyFile
parseOWL filename = do
    let jar = "OWL2Parser.jar"
    absfile <- if checkUri filename then return filename else
      fmap ("file://" ++) $ canonicalizePath filename
    (hasJar, toolPath) <- check4HetsOWLjar jar
    if hasJar then do
       (exitCode, result, errStr) <- executeProcess "java"
         ["-jar", toolPath </> jar, absfile, "xml"] ""
       case (exitCode, errStr) of
         (ExitSuccess, "") -> return $ parseProc filename result
         _ -> error $ "process stop! " ++ shows exitCode "\n"
              ++ errStr
      else error $ jar
        ++ " not found, check your environment variable: " ++ hetsOWLenv

parseProc :: FilePath -> String -> LIB_DEFN
parseProc filename str =
  let es = onlyElems $ parseXML str
      imap = Map.fromList . map (\ e -> let
        Just imp = findAttr (unqual "name") e
        Just ont = findAttr (unqual "ontiri") e
        in (imp, ont)) $ concatMap (filterElementsName $ isSmth "Loaded") es
  in convertToLibDefN filename
        . unifyDocs . map (xmlBasicSpec imap)
        $ concatMap (filterElementsName $ isSmth "Ontology") es

cnvtoSimpleId :: QName -> SPEC_NAME
cnvtoSimpleId = simpleIdToIRI . mkSimpleId . filter isAlphaNum . showQN

createSpec :: OntologyDocument -> Annoted SPEC
createSpec o = addImports (map cnvtoSimpleId . imports $ ontology o)
  . makeSpec $ G_basic_spec OWL2 o

convertone :: OntologyDocument -> Annoted LIB_ITEM
convertone o = makeSpecItem (cnvtoSimpleId $ name $ ontology o) $ createSpec o

convertToLibDefN :: FilePath -> [OntologyDocument] -> LIB_DEFN
convertToLibDefN filename l = Lib_defn
  (emptyLibName $ convertFileToLibStr filename)
  (makeLogicItem OWL2 : map convertone l) nullRange []
