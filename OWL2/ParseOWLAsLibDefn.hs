{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

analyse OWL files by calling the external Java parser.
-}

module OWL2.ParseOWLAsLibDefn (parseOWL, convertOWL, writeOWLFile) where

import OWL2.AS
import OWL2.MS
import OWL2.Rename

import qualified Data.ByteString.Lazy as L
import Data.List
import Data.Maybe
import qualified Data.Map as Map

import Common.XmlParser
import Common.Id
import Common.IRI
import Common.LibName
import Common.ProverTools
import Common.AS_Annotation
import Common.Utils

import Control.Monad

import Logic.Grothendieck
import OWL2.Logic_OWL2
import OWL2.XML

import Syntax.AS_Library
import Syntax.AS_Structured

import System.Directory
import System.Exit
import System.FilePath

import Text.XML.Light hiding (QName)

-- | call for owl parser (env. variable $HETS_OWL_TOOLS muss be defined)
parseOWL :: Bool                  -- ^ Sets Option.quick
         -> String                -- ^ Input-Type (OMN, OWL-Xml, RDF, OBO, ..)
         -> FilePath              -- ^ local filepath or uri
         -> IO [LIB_DEFN]         -- ^ map: uri -> OntologyFile
parseOWL quick itype fn = do
    tmpFile <- getTempFile "" "owlTemp.xml"
    (exitCode, _, errStr) <- parseOWLAux quick fn ["-o", "xml", tmpFile]
    case (exitCode, errStr) of
      (ExitSuccess, "") -> do
          cont <- L.readFile tmpFile
          removeFile tmpFile
          parseProc cont
      _-> error $ "process stop! " ++ shows exitCode "\n" ++ errStr

parseOWLAux :: Bool         -- ^ Sets Option.quick
         -> FilePath        -- ^ local filepath or uri
         -> [String]        -- ^ arguments for java parser 
         -> IO (ExitCode, String, String)
parseOWLAux quick fn args = do
    let jar = "OWL2Parser.jar"
    (hasJar, toolPath) <- check4HetsOWLjar jar
    if hasJar then executeProcess "java" (["-jar", toolPath </> jar]
        ++ args ++ [fn] ++ if quick then ["-qk"] else []) ""
    else error $ jar
        ++ " not found, check your environment variable: " ++ hetsOWLenv

-- | converts owl file to desired syntax using owl-api
convertOWL :: FilePath -> String -> IO (String)
convertOWL fn tp = do
  (exitCode, content, errStr) <- parseOWLAux False fn ["-o-sys", tp]
  case (exitCode, errStr) of
    (ExitSuccess, "") -> return content
    _-> error $ "process stop! " ++ shows exitCode "\n" ++ errStr

parseProc :: L.ByteString -> IO [LIB_DEFN]
parseProc str = do
  res <- parseXml str
  let es = elChildren $ either error id res
      mis = concatMap (filterElementsName $ isSmth "Missing") es
      imap = Map.fromList . mapMaybe (\ e -> do
        imp <- findAttr (unqual "name") e
        ont <- findAttr (unqual "ontiri") e
        return (imp, ont)) $ concatMap (filterElementsName $ isSmth "Loaded") es
  unless (null mis) . putStrLn $ "Missing imports: "
    ++ intercalate ", " (map strContent mis)
  return . map (convertToLibDefN imap)
        . unifyDocs . map (xmlBasicSpec imap)
        $ concatMap (filterElementsName $ isSmth "Ontology") es

qNameToIRI :: QName -> SPEC_NAME
qNameToIRI qn = let s = showQN qn in
  fromMaybe (error $ "qNameToIRI " ++ s) $ parseIRIManchester s

createSpec :: OntologyDocument -> [SPEC_NAME] -> Annoted SPEC
createSpec o imps = addImports imps . makeSpec $ G_basic_spec OWL2 o

convertone :: OntologyDocument -> SPEC_NAME -> [SPEC_NAME] -> Annoted LIB_ITEM
convertone o oname i = makeSpecItem oname $ createSpec o i

convertToLibDefN :: Map.Map String String -> OntologyDocument -> LIB_DEFN
convertToLibDefN imap o = Lib_defn ln
    (makeLogicItem OWL2 : imp_libs ++ [convertone o oname imps2]) nullRange []
  where ont = ontology o
        il = Map.toList imap
        is = map snd il
        ln = case lookup libstr $ map (\ (a, b) -> (b, a)) il of
            Just s -> setFilePath s
            Nothing -> setFilePath libstr
          $ iriLibName oname
        imps = map qNameToIRI $ imports ont
        imps2 = filter ((`elem` is) . show . setAngles False) imps
        oname = qNameToIRI $ name ont
        libstr = show $ setAngles False oname
        imp_libs = map (addDownload False) imps2
