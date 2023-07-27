{- |
Module      :  ./Driver/AnaLib.hs
Description :  wrapper for static analysis of DOL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

wrapper for static analysis of DOL reading and writing prf-files
-}

module Driver.AnaLib
    ( anaLib
    , anaLibExt
    , anaLibReadPrfs
    ) where

import Common.Utils (FileInfo(..))

import Proofs.Automatic
import Proofs.NormalForm

import Static.DevGraph
import Static.History
import Static.AnalysisLibrary
import Static.ApplyChanges
import Static.FromXml
import System.Directory (removeFile)

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
anaLib opts origName = do
  let fname = useCatalogURL opts origName
      isPrfFile = isSuffixOf prfSuffix
  ep <- getContentAndFileType opts {intype = GuessIn}
    $ if isPrfFile fname then rmSuffix fname else fname
  case ep of
    Left _ -> anaLibExt opts fname emptyLibEnv emptyDG
    Right (_, _, fInfo, content)
      | isPrfFile (filePath fInfo) -> do
          putIfVerbose opts 0 $ "a matching source file for proof history '"
                           ++ (filePath fInfo) ++ "' not found."
          when (wasDownloaded fInfo) $ removeFile (filePath fInfo)
          return Nothing
      | isDgXmlFile opts (filePath fInfo) content -> do
          res <- readDGXml opts (filePath fInfo)
          when (wasDownloaded fInfo) $ removeFile (filePath fInfo)
          return res
      | otherwise -> do
          res <- anaLibExt opts (keepOrigClifName opts origName (filePath fInfo))
            emptyLibEnv emptyDG
          when (wasDownloaded fInfo) $ removeFile (filePath fInfo)
          return res

-- | read a file and extended the current library environment
anaLibExt :: HetcatsOpts -> FilePath -> LibEnv -> DGraph
  -> IO (Maybe (LibName, LibEnv))
anaLibExt opts file libEnv initDG = do
    Result ds res <- runResultT $ anaLibFileOrGetEnv (logicGraphForFile file) opts
      Set.empty libEnv initDG Nothing file
    showDiags opts ds
    case res of
        Nothing -> return Nothing
        Just (ln, lenv) -> do
            let envRes = if computeNormalForm opts then normalForm ln lenv else
                  return lenv
                envN = fromMaybe lenv $ maybeResult envRes
                nEnv = if applyAutomatic opts || hasPrfOut opts
                       then automatic ln envN else envN
                xd = xupdate opts
            showDiags opts $ diags envRes
            p <- if null xd then return (ln, nEnv) else do
              putIfVerbose opts 2 $ "Reading " ++ xd
              xs <- readFile xd
              Result es mdg <- runResultT $ dgXUpdate opts xs nEnv ln
                (lookupDGraph ln nEnv)
              showDiags opts es
              return $ fromMaybe (ln, nEnv) mdg
            return $ Just p

readPrfFile :: HetcatsOpts -> LibEnv -> LibName -> IO LibEnv
readPrfFile opts ps ln = do
    let fname = libNameToFile ln
        prfFile = rmSuffix fname ++ prfSuffix
    recent <- checkRecentEnv opts prfFile fname
    h <- if recent then
          fmap (fromMaybe SizedList.empty)
            $ readVerbose logicGraph opts (Just ln) prfFile
       else return SizedList.empty
    return $ Map.update (Just . applyProofHistory h) ln ps

readPrfFiles :: HetcatsOpts -> LibEnv -> IO LibEnv
readPrfFiles opts le = foldM (readPrfFile opts) le $ Map.keys le
