{- |
Module      :  $Header$
Description :  Types for the Central GUI of Hets
Copyright   :  (c) Jorina Freya Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module GUI.GraphTypes
    ( GInfo(..)
    , InternalNames(..)
    , ConvFunc
    , LibFunc
    , DaVinciGraphTypeSyn
    , emptyGInfo
    , copyGInfo
    , lockGlobal
    , tryLockGlobal
    , unlockGlobal
    )
    where

import GUI.GraphAbstraction(GraphInfo, initgraphs)
import GUI.ProofManagement (GUIMVar)

import Syntax.AS_Library
import Syntax.Print_AS_Library()

import Static.DevGraph

import Common.Id(nullRange)

import Driver.Options(HetcatsOpts, defaultHetcatsOpts)

import Data.IORef

import Control.Concurrent.MVar

import DaVinciGraph
import GraphDisp

data InternalNames = InternalNames
                     { showNames :: Bool
                     , updater :: [(String,(String -> String) -> IO ())]
                     }

-- | Global datatype for all GUI functions
data GInfo = GInfo
             { -- Global
               libEnvIORef :: IORef LibEnv
             , gi_hetcatsOpts :: HetcatsOpts
             , windowCount :: MVar Integer
             , exitMVar :: MVar ()
             , globalLock :: MVar ()
             , globalHist :: MVar ([[LIB_NAME]],[[LIB_NAME]])
             , functionLock :: MVar ()
               -- Local
             , gi_LIB_NAME :: LIB_NAME
             , gi_GraphInfo :: GraphInfo
             , internalNamesIORef :: IORef InternalNames
             , proofGUIMVar :: GUIMVar
             }

{- | Type of the convertGraph function. Used as type of a parameter of some
     functions in GraphMenu and GraphLogic. -}
type ConvFunc = GInfo -> String -> LibFunc -> IO ()

type LibFunc =  GInfo -> IO DaVinciGraphTypeSyn

type DaVinciGraphTypeSyn =
     Graph DaVinciGraph
           DaVinciGraphParms
           DaVinciNode
           DaVinciNodeType
           DaVinciNodeTypeParms
           DaVinciArc
           DaVinciArcType
           DaVinciArcTypeParms

-- | Creates an empty GInfo
emptyGInfo :: IO GInfo
emptyGInfo = do
  iorLE <- newIORef emptyLibEnv
  graphInfo <- initgraphs
  iorIN <- newIORef $ InternalNames False []
  guiMVar <- newEmptyMVar
  gl <- newEmptyMVar
  fl <- newEmptyMVar
  exit <- newEmptyMVar
  wc <- newMVar 0
  gh <- newMVar ([],[])
  return $ GInfo { libEnvIORef = iorLE
                  , gi_LIB_NAME = Lib_id $ Indirect_link "" nullRange "" noTime
                 , gi_GraphInfo = graphInfo
                 , internalNamesIORef = iorIN
                 , gi_hetcatsOpts = defaultHetcatsOpts
                 , proofGUIMVar = guiMVar
                 , windowCount = wc
                 , exitMVar = exit
                 , globalLock = gl
                 , globalHist = gh
                 , functionLock = fl
                 }

-- | Creates an empty GInfo
copyGInfo :: GInfo -> IO GInfo
copyGInfo gInfo = do
  graphInfo <- initgraphs
  iorIN <- newIORef $ InternalNames False []
  guiMVar <- newEmptyMVar
  return $ gInfo { gi_LIB_NAME = Lib_id $ Indirect_link "" nullRange "" noTime
                 , gi_GraphInfo = graphInfo
                 , internalNamesIORef = iorIN
                 , proofGUIMVar = guiMVar
                 }

{- | Acquire the global lock. If already locked it waits till it is unlocked
     again.-}
lockGlobal :: GInfo -> IO ()
lockGlobal (GInfo { globalLock = lock }) = putMVar lock ()

-- | Tries to acquire the global lock. Return False if already acquired.
tryLockGlobal :: GInfo -> IO Bool
tryLockGlobal (GInfo { globalLock = lock }) = tryPutMVar lock ()

-- | Releases the global lock.
unlockGlobal :: GInfo -> IO ()
unlockGlobal (GInfo { globalLock = lock }) = do
  unlocked <- tryTakeMVar lock
  case unlocked of
    Just () -> return ()
    Nothing -> error "Global lock wasn't locked."
