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

import Data.List
import Data.Maybe
import qualified Data.Map as Map

import Common.Id
import Common.IRI
import Common.LibName
import Common.ProverTools
import Common.AS_Annotation
import Common.Utils

import Logic.Grothendieck
import OWL2.Logic_OWL2
import OWL2.XML

import Driver.Options

import Syntax.AS_Library
import Syntax.AS_Structured

import System.Directory
import System.Exit
import System.FilePath

import Text.XML.Light hiding (QName)

-- | call for owl parser (env. variable $HETS_OWL_TOOLS muss be defined)
parseOWL :: FilePath              -- ^ local filepath or uri
         -> IO [LIB_DEFN]         -- ^ map: uri -> OntologyFile
parseOWL fn = do
    let jar = "OWL2Parser.jar"
    absfile <- if checkUri fn then return fn else
      fmap ("file://" ++) $ canonicalizePath fn
    (hasJar, toolPath) <- check4HetsOWLjar jar
    if hasJar then do
        (exitCode, result, errStr) <- executeProcess "java"
          ["-jar", toolPath </> jar, absfile, "xml"] ""
        case (exitCode, errStr) of
          (ExitSuccess, "") -> return $ parseProc fn result
          _ -> error $ "process stop! " ++ shows exitCode "\n"
              ++ errStr
      else error $ jar
        ++ " not found, check your environment variable: " ++ hetsOWLenv

parseProc :: FilePath -> String -> [LIB_DEFN]
parseProc fp str =
  let es = onlyElems $ parseXML str
      imap = Map.fromList . mapMaybe (\ e -> do
        imp <- findAttr (unqual "name") e
        ont <- findAttr (unqual "ontiri") e
        return (imp, ont)) $ concatMap (filterElementsName $ isSmth "Loaded") es
  in map (convertToLibDefN fp imap)
        . unifyDocs . map (xmlBasicSpec imap)
        $ concatMap (filterElementsName $ isSmth "Ontology") es

qNameToIRI :: QName -> SPEC_NAME
qNameToIRI qn = let s = showQN qn in
  fromMaybe (error $ "qNameToIRI " ++ s) $ parseIRIManchester s

createSpec :: OntologyDocument -> [SPEC_NAME] -> Annoted SPEC
createSpec o imps = addImports imps . makeSpec $ G_basic_spec OWL2 o

convertone :: OntologyDocument -> SPEC_NAME -> [SPEC_NAME] -> Annoted LIB_ITEM
convertone o oname i = makeSpecItem oname $ createSpec o i

convertToLibDefN :: FilePath -> Map.Map String String -> OntologyDocument
  -> LIB_DEFN
convertToLibDefN fp imap o = Lib_defn ln
    (makeLogicItem OWL2 : imp_libs ++ [convertone o oname imps2]) nullRange []
  where ont = ontology o
        isGenPrefix = isPrefixOf "inputstream:ontology"
        il = Map.toList imap
        is = map snd il
        ln = case lookup libstr $ map (\ (a, b) -> (b, a)) il of
            Just s | isGenPrefix s -> id
            Just s -> setFilePath s
            Nothing -> setFilePath libstr
          $ iriLibName oname
        imps = map qNameToIRI $ imports ont
        imps2 = filter ((`elem` is) . show . setAnkles False) imps
        oname1 = qNameToIRI $ name ont
        libstr = show $ setAnkles False oname1
        oname = if isGenPrefix libstr then filePathToLibId fp else oname1
        imp_libs = map (addDownload False) imps2
