{- |
Module      :  $Header$
Description :  Analyzes a logic definition
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.Analysis ( anaLogicDef ) where

import System.Directory
import System.FilePath

import Network.URI

import Static.DevGraph
import Static.GTheory

import Logic.Grothendieck
import Logic.ExtSign

import Framework.SignCat
import Framework.Parse
import Framework.Logic_Framework

import Data.List
import qualified Data.Map as Map

import Common.LibName
import Control.Monad
import Driver.Options

--import Debug.Trace

-- resolves the first file path wrt to the second
resolve :: FilePath -> FilePath -> FilePath
resolve fp1 fp2 =
  case parseURIReference fp1 of
    Nothing -> error "Invalid file name."
    Just uri1 -> do
      case parseURIReference fp2 of
        Nothing -> error "Invalid file name."
        Just uri2 -> do
          case relativeTo uri1 uri2 of
               Nothing -> error "Invalid file name."
               Just f -> show f

-- analyzes a logic definition
anaLogicDef :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaLogicDef _ fp = do
  dir <- getCurrentDirectory
  let file = resolve fp (dir ++ "/")
  str <- readFile file
  error str 
  sig <- parseLogicDef str
  let dg = makeDG sig
  let name = emptyLibName file
  let libs = Map.insert name dg emptyLibEnv
  return $ Just (name,libs)

-- generates a single-node dgraph for the logic definition
makeDG :: Sign -> DGraph
makeDG ldef = do
  let node = getNewNodeDG emptyDG
      nodeName = emptyNodeName { getName = logicName ldef }
      info = newNodeInfo DGBasic
      extSign = makeExtSign Framework ldef
      gth = noSensGTheory Framework extSign startSigId
      nodeLabel = newInfoNodeLab nodeName info gth
      in insNodeDG (node,nodeLabel) emptyDG

