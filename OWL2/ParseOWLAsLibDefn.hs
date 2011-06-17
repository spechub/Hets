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
import OWL2.FS
import OWL2.FunctionalParser
import OWL2.Logic_OWL2

import Common.Id
import Common.LibName
import Common.ProverTools
import Common.AS_Annotation hiding (isAxiom, isDef)


import Driver.Options

import Syntax.AS_Library
import Syntax.AS_Structured

import Logic.Grothendieck

import System.Directory
import System.Exit
import System.FilePath
import System.Process

import Text.ParserCombinators.Parsec
import Common.Parsec


-- | call for owl parser (env. variable $HETS_OWL_TOOLS muss be defined)
parseOWL :: FilePath              -- ^ local filepath or uri
         -> IO LIB_DEFN        -- ^ map: uri -> OntologyFile
parseOWL filename = do
    let jar = "OWL2Parser.jar"
    absfile <- if checkUri filename then return filename else
      fmap ("file://" ++) $ canonicalizePath filename
    (hasJar, toolPath) <- check4HetsOWLjar jar
    if hasJar then do
       (exitCode, result, errStr) <- readProcessWithExitCode "java"
         ["-jar", toolPath </> jar, absfile] ""
       case exitCode of
         ExitSuccess -> parseProc filename result
         _ -> error $ "process stop! " ++ shows exitCode "\n"
              ++ errStr
      else error $ jar ++ " not found"

-- | parse the tmp-omn-file from java-owl-parser
parseProc :: FilePath -> String -> IO LIB_DEFN
parseProc filename str = do
    case runParser (many1 ontologyFile << eof) () filename str of
      Right os -> return $ convertToLibDefN filename os 
      Left err -> do
        putStrLn str
        fail $ show err

convertone :: OntologyFile-> Annoted LIB_ITEM
convertone o = emptyAnno $ Spec_defn  
  (mkSimpleId $ showQN $ uri $ ontology o) 
  emptyGenericity
  (emptyAnno $ Basic_spec (G_basic_spec OWL2 o ) nullRange)
  nullRange 

convertToLibDefN :: FilePath -> [OntologyFile] -> LIB_DEFN
convertToLibDefN filename l = Lib_defn 
  (emptyLibName $ convertFileToLibStr filename)
  (map convertone $ l)
  nullRange
  []
