{- |
Module      :  ./Comorphisms/GetPreludeLib.hs
Description :  read a prelude library for some comorphisms
Copyright   :  (c) Christian Maeder and DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

read a prelude library for some comorphisms
-}

module Comorphisms.GetPreludeLib where

import Static.AnalysisLibrary
import Driver.Options
import Driver.ReadFn
import Comorphisms.LogicList

import Static.ComputeTheory

import Static.DevGraph
import Static.GTheory

import Common.Result
import Common.ResultT
import Common.Utils
import qualified Control.Monad.Fail as Fail

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import System.FilePath

readLib :: FilePath -> IO [G_theory]
readLib fp0 = do
  lib <- getEnvDef "HETS_LIB" ""
  let opts = defaultHetcatsOpts { libdirs = splitPaths lib }
      fp = lib </> fp0
  Result _ mLib <- runResultT $ anaLibFileOrGetEnv preLogicGraph
    opts Set.empty Map.empty emptyDG (fileToLibName opts fp) fp
  case mLib of
    Nothing -> Fail.fail $ "library could not be read from: " ++ fp
    Just (ln, le) -> do
      let dg = lookupDGraph ln le
      return . catMaybes . Map.fold (\ ge -> case ge of
        SpecEntry (ExtGenSig _ (NodeSig n _)) ->
           if null $ outDG dg n then (computeTheory le ln n :)
           else id
        _ -> id) [] $ globalEnv dg
