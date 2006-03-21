{- |
Module      :  $Header$
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Interface for accessing Hets-System
-}

module OMDoc.HetsInterface
  (
    , module OMDoc.HetsDefs
    , module Driver.ReadFn
    , module Driver.WriteFn
    , showGraph
    , run
    , runLib
    , getDG
  )
  where

import OMDoc.HetsDefs

import Syntax.AS_Library --(LIB_NAME(),LIB_DEFN()) 
import Driver.ReadFn
import Driver.WriteFn

import Driver.Options

import Static.AnalysisLibrary

import Static.DevGraph

import qualified Common.Lib.Map as Map

import qualified GUI.ShowGraph as GUI

-- | "alias" for GUI.showGraph (for export)
showGraph::FilePath->HetcatsOpts->Maybe (LIB_NAME, LibEnv)->IO ()
showGraph file opt env =
	case env of
		Just (ln, libenv) -> do
			GUI.showGraph file opt (Just (ln, libenv))
		Nothing -> return ()

-- |  run 'anaLib' with default HetcatsOptions 
run :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
run file = anaLib dho file

-- | run 'anaLib' with default HetcatsOptions + include directory 
runLib::FilePath->FilePath->IO (Maybe (LIB_NAME, LibEnv))
runLib lib file = anaLib (dho { libdir = lib }) file

-- | try to load a DevGraph via Hets and return only the DevGraph for the 
-- first library
getDG::FilePath->IO DGraph
getDG f = do
	(Just (ln,lenv)) <- run f
	case Map.lookup ln lenv of
		Nothing -> error "Error looking op DGraph"
		(Just gc) -> return $ devGraph gc

