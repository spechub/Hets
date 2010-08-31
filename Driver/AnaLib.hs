{- |
Module      :  $Header$
Description :  wrapper for static analysis of HetCASL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

wrapper for static analysis of HetCASL reading and writing prf-files
-}

module Driver.AnaLib
    ( anaLib
    , anaLibExt
    , anaLibReadPrfs
    ) where

import Proofs.Automatic
import Proofs.NormalForm

import Static.DevGraph
import Static.History
import Static.AnalysisLibrary

import Comorphisms.LogicGraph

import Common.Result
import Common.ResultT
import Common.LibName
import qualified Common.Lib.SizedList as SizedList

import Driver.Options
import Driver.ReadFn

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (isSuffixOf)
import Control.Monad
import Data.Maybe

anaLibReadPrfs :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaLibReadPrfs opts file = do
    m <- anaLib opts
      { outtypes = []
      , specNames = []
      , modelSparQ = ""
      , dumpOpts = [] } file
    case m of
      Nothing -> return Nothing
      Just (ln, libEnv) -> do
        nEnv <- readPrfFiles opts libEnv
        return $ Just (ln, nEnv)

-- | lookup an env or read and analyze a file
anaLib :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaLib opts fname = do
  fname' <- existsAnSource opts {intype = GuessIn} $ rmSuffix fname
  case fname' of
    Nothing -> anaLibExt opts fname emptyLibEnv emptyDG
    Just file ->
        if isSuffixOf prfSuffix file then do
            putIfVerbose opts 0 $ "a matching source file for proof history '"
                             ++ file ++ "' not found."
            return Nothing
        else anaLibExt opts file emptyLibEnv emptyDG

-- | read a file and extended the current library environment
anaLibExt :: HetcatsOpts -> FilePath -> LibEnv -> DGraph
  -> IO (Maybe (LibName, LibEnv))
anaLibExt opts file libEnv initDG = do
    Result ds res <- runResultT $ anaLibFileOrGetEnv logicGraph opts
      Set.empty libEnv initDG (fileToLibName opts file) file
    showDiags opts ds
    case res of
        Nothing -> return Nothing
        Just (ln, lenv) -> do
            let envRes = if computeNormalForm opts then normalForm ln lenv else
                  return lenv
                envN = fromMaybe lenv $ maybeResult envRes
                nEnv = if applyAutomatic opts || hasPrfOut opts
                       then automatic ln envN else envN
            showDiags opts $ diags envRes
            return $ Just (ln, nEnv)

readPrfFile :: HetcatsOpts -> LibEnv -> LibName -> IO LibEnv
readPrfFile opts ps ln = do
    let fname = libNameToFile ln
        prfFile = rmSuffix fname ++ prfSuffix
    recent <- checkRecentEnv opts prfFile fname
    h <- if recent then
          fmap (fromMaybe SizedList.empty)
            $ readVerbose logicGraph opts ln prfFile
       else return SizedList.empty
    return $ Map.update (Just . applyProofHistory h) ln ps

readPrfFiles :: HetcatsOpts -> LibEnv -> IO LibEnv
readPrfFiles opts le = foldM (readPrfFile opts) le $ Map.keys le
