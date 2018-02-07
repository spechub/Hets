{-# LANGUAGE CPP #-}
{- |
Module      :  ./Common/Timing.hs
Description :  utility module for measuring execution time
Copyright   :  (c) C. Maeder DFKI GmbH
License     :  GPLv2 or higher, see LICENSE.txt

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

import Data.Fixed
import Data.Time
import Control.Monad
import Numeric

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

measureWallTime :: IO a -> IO (a, TimeOfDay)
measureWallTime f = do
  startTime <- getHetsTime
  result <- f
  endTime <- getHetsTime
  let wallTimeUsed = diffHetsTime endTime startTime
  return (result, wallTimeUsed)

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

timeOfDayToSeconds :: TimeOfDay -> Int
timeOfDayToSeconds TimeOfDay { todHour = hours
                             , todMin = minutes
                             , todSec = seconds
                             } =
  (floor . toDouble) seconds + 60 * (minutes + 60 * hours)
  where
    toDouble :: Pico -> Double
    toDouble s = case readSigned readFloat $ show s of
      [(x, "")] -> x
      _ -> error $ "timeOfDayToSeconds: Failed reading the number " ++ show s
