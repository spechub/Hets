{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  utility module for measuring execution time
Copyright   :  (c) C. Maeder DFKI GmbH
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Utility functions that can't be found in the libraries
               but should be shared across Hets.
-}

module Common.Timing where

#ifdef UNIX
import System.Posix.Time
import System.Posix.Types
#else
import Data.Time.Clock
#endif

import Data.Time
import Control.Monad

newtype HetsTime = HetsTime
#ifdef UNIX
  EpochTime
#else
  UTCTime
#endif

getHetsTime :: IO HetsTime
getHetsTime = liftM HetsTime
#ifdef UNIX
  epochTime
#else
  getCurrentTime
#endif

diffHetsTime :: HetsTime -> HetsTime -> TimeOfDay
diffHetsTime (HetsTime t1) (HetsTime t2) =
   timeToTimeOfDay $ secondsToDiffTime $ round
   (realToFrac (
#ifdef UNIX
   (-)
#else
   diffUTCTime
#endif
               t1 t2) :: Double)
