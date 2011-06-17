{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

analyse OWL files by calling the external Java parser.
-}

module OWL2.OWLAnalysis (parseOWL) where

import OWL2.AS
import OWL2.Parse

import Static.GTheory
import Static.DevGraph
import Static.ComputeTheory

import Common.Id
import Common.GlobalAnnotations
import Common.ExtSign
import Common.LibName
import Common.Result
import Common.ProverTools
import Common.Utils
import Common.AS_Annotation hiding (isAxiom, isDef)
--import ATerm.ReadWrite
--import ATerm.Unshared

import Driver.Options

import Logic.Comorphism
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover

import System.Directory
import System.Exit
import System.FilePath
import System.Process

import Text.ParserCombinators.Parsec
import Common.Parsec

import qualified Data.Map as Map
import qualified Data.List as List
import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Query.DFS as DFS
import qualified Data.Graph.Inductive.Query.BFS as BFS
import Data.Maybe (fromJust)


-- | call for owl parser (env. variable $HETS_OWL_TOOLS muss be defined)
parseOWL :: FilePath              -- ^ local filepath or uri
         -> IO OntologyMap        -- ^ map: uri -> OntologyFile
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
parseProc :: FilePath -> String -> IO OntologyMap
parseProc filename str = do
    case runParser (many1 basicSpec << eof) () filename str of
      Right os -> return $ Map.fromList
        $ map (\ o -> (showQN $ uri $ ontology o, o)) os
      Left err -> do
        print err
        putStrLn str
        return Map.empty

