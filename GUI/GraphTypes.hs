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
    , Colors(..)
    , colors
    , emptyGInfo
    , copyGInfo
    , lockGlobal
    , tryLockGlobal
    , unlockGlobal
    )
    where

import GUI.GraphAbstraction(GraphInfo, initgraphs)
import GUI.ProofManagement (GUIMVar)
import GUI.History(CommandHistory, emptyCommandHistory)

import Static.DevGraph

import Common.LibName
import Common.Id(nullRange)

import Driver.Options(HetcatsOpts(uncolored), defaultHetcatsOpts)

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
             , commandHist :: CommandHistory
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

{- | Colors to use. From dark to bright.
     Names are structured:
       color,
       maybe number (higher number is brighter),
       D for dark version of color and B for bright version -}
data Colors = Colors
  { blackD :: String
  , blackB :: String
  , blue1D :: String
  , blue1B :: String
  , blue2D :: String
  , blue2B :: String
  , coral1D :: String
  , coral1B :: String
  , coral2D :: String
  , coral2B :: String
  , green1D :: String
  , green1B :: String
  , green2D :: String
  , green2B :: String
  , yellowD :: String
  , yellowB :: String
  , khakiD :: String
  , khakiB :: String
  }

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
  ch <- emptyCommandHistory
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
                 , commandHist = ch
                 , functionLock = fl
                 }

-- | Creates an empty GInfo
copyGInfo :: GInfo -> LIB_NAME -> IO GInfo
copyGInfo gInfo newLN = do
  graphInfo <- initgraphs
  iorIN <- newIORef $ InternalNames False []
  guiMVar <- newEmptyMVar
  return $ gInfo { gi_LIB_NAME = newLN
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

-- | Generates the colortable
colors :: HetcatsOpts -> Colors
colors opts = Colors
  { blackD  = getColor opts ("gray0",           "gray0")
  , blackB  = getColor opts ("gray30",          "gray5")
  , blue1D  = getColor opts ("RoyalBlue3",      "gray20")
  , blue1B  = getColor opts ("RoyalBlue1",      "gray23")
  , blue2D  = getColor opts ("SteelBlue3",      "gray27")
  , blue2B  = getColor opts ("SteelBlue1",      "gray30")
  , coral1D = getColor opts ("coral3",          "gray40")
  , coral1B = getColor opts ("coral1",          "gray43")
  , coral2D = getColor opts ("LightSalmon2",    "gray47")
  , coral2B = getColor opts ("LightSalmon",     "gray50")
  , green1D = getColor opts ("MediumSeaGreen",  "gray60")
  , green1B = getColor opts ("PaleGreen3",      "gray63")
  , green2D = getColor opts ("PaleGreen2",      "gray67")
  , green2B = getColor opts ("LightGreen",      "gray70")
  , yellowD = getColor opts ("gold2",           "gray78")
  , yellowB = getColor opts ("gold",            "gray81")
  , khakiD  = getColor opts ("LightGoldenrod3", "gray85")
  , khakiB  = getColor opts ("LightGoldenrod",  "gray88")
  }

-- | Converts colors to grayscale if needed
getColor :: HetcatsOpts -> (String, String) -> String
getColor opts (cname, gname) = if uncolored opts then gname else cname
