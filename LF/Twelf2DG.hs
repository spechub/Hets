{- |
Module      :  $Header$
Description :  Maude Development Graphs
Copyright   :  (c) Adrian Riesco, Facultad de Informatica UCM 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  portable

Conversion of Maude to Development Graphs.
-}

module LF.Twelf2DG where

import System.Exit
import System.IO
import System.Process

import Static.GTheory
import Static.DevGraph
import Static.ComputeTheory
import Static.AnalysisStructured

import Logic.Logic
import Logic.Prover
import Logic.ExtSign
import Logic.Grothendieck

import LF.Sign
import LF.Morphism

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Graph.Inductive.Graph

import Common.Consistency
import Common.Id
import Common.Result
import Common.LibName
import Common.AS_Annotation
import Common.Utils

import Driver.Options

-- path to the Twelf folder must be set in the environment variable TWELF_LIB
twelf :: String
twelf = "check-some"
options :: [String]
options = ["-omdoc", "."]

{- generates a development graph from the path of a
   Twelf file -}
directTwelfParsing :: FilePath -> IO DGraph
directTwelfParsing file = do
  path <- getEnvDef "TWELF_LIB" ""
  if null path then error "environment variable TWELF_LIB is not set" else do
    (hIn, hOut, _, procH) <- runInteractiveProcess (concat [path, "/" ,twelf])
                                                   (options ++ [file])
                                                   Nothing
                                                   Nothing 
    exitCode <- getProcessExitCode procH
    case exitCode of
      Nothing -> do
              return $ emptyDG
      Just ExitSuccess -> error "Twelf terminated immediately."
      Just (ExitFailure i) ->
          error $ "Calling Twelf failed with exitCode: " ++ show i

-- generates a library from the path of a Twelf file
anaTwelfFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaTwelfFile _ file = do
    dg <- directTwelfParsing file
    let name = emptyLibName ""
    return $ Just (name, 
                   Map.singleton name $ computeDGraphTheories Map.empty dg)
