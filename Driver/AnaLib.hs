{- |
Module      :  $Header$
Description :  wrapper for static analysis of HetCASL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
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
import Proofs.EdgeUtils

import Static.DevGraph
import Static.AnalysisLibrary

import Comorphisms.LogicGraph

import Common.Result
import Common.ResultT
import Common.LibName

import Driver.Options
import Driver.ReadFn
import Driver.WriteFn

import qualified Data.Map as Map
import Data.List (isSuffixOf)
import Control.Monad

anaLibReadPrfs :: HetcatsOpts -> FilePath -> IO (Maybe (LIB_NAME, LibEnv))
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
        writeSpecFiles (removePrfOut opts) file nEnv ln $ lookupDGraph ln nEnv
        return $ Just (ln, nEnv)

-- | lookup an env or read and analyze a file
anaLib :: HetcatsOpts -> FilePath -> IO (Maybe (LIB_NAME, LibEnv))
anaLib opts fname = do
  fname' <- existsAnSource opts {intype = GuessIn} $ rmSuffix fname
  case fname' of
    Nothing -> anaLibExt opts fname emptyLibEnv
    Just file ->
        if isSuffixOf prfSuffix file then do
            putIfVerbose opts 0 $ "a matching source file for proof history '"
                             ++ file ++ "' not found."
            return Nothing
        else anaLibExt opts file emptyLibEnv

-- | read a file and extended the current library environment
anaLibExt :: HetcatsOpts -> FilePath -> LibEnv -> IO (Maybe (LIB_NAME, LibEnv))
anaLibExt opts file libEnv = do
    Result ds res <- runResultT $ anaLibFileOrGetEnv logicGraph opts
                     libEnv (fileToLibName opts file) file
    showDiags opts ds
    case res of
        Nothing -> return Nothing
        Just (ln, lenv) -> do
            let nEnv = if hasPrfOut opts then automatic ln lenv else lenv
            writeSpecFiles opts file nEnv ln $ lookupDGraph ln nEnv
            return $ Just (ln, nEnv)

readPrfFile :: HetcatsOpts -> LibEnv -> LIB_NAME -> IO LibEnv
readPrfFile opts ps ln = do
    let fname = libNameToFile opts ln
        prfFile = rmSuffix fname ++ prfSuffix
    recent <- checkRecentEnv opts prfFile fname
    h <- if recent then
          fmap (maybe [emptyHistory] id) $ readVerbose opts ln prfFile
       else return [emptyHistory]
    return $ Map.update (Just . applyProofHistory h) ln ps

readPrfFiles :: HetcatsOpts -> LibEnv -> IO LibEnv
readPrfFiles opts le = do
    foldM (readPrfFile opts) le $ Map.keys le
