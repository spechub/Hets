{- |
Module      :  ./TPTP/Prover/Vampire/ProofParser.hs
Description :  Parses a Vampire proof.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.Vampire.ProofParser ( parseStatus
                                       , parseTimeUsed
                                       , filterProofLines
                                       ) where

import Common.Utils

import Data.Char
import Data.List hiding (lines)
import Data.Maybe
import Data.Time (TimeOfDay (..), midnight)
import Prelude hiding (lines)

parseStatus :: [String] -> String
parseStatus = fromMaybe "Unknown" . foldr parseStatusIfStatusline Nothing
  where
    parseStatusIfStatusline :: String -> Maybe String -> Maybe String
    parseStatusIfStatusline line mStatus = case mStatus of
      Nothing -> case () of
        _ | isPrefixOf "Termination reason: Time limit" line -> Just "Timeout"
        _ | isPrefixOf "Termination reason: Memory limit" line -> Just "MemoryOut"
        _ | isPrefixOf "Termination reason: Refutation not found" line -> Just "GaveUp"
        _ | isPrefixOf "Termination reason: Refutation" line -> Just "Theorem"
        _ | isPrefixOf "Termination reason: Satisfiable" line -> Just "CounterSatisfiable" -- this is a model
        _ | isPrefixOf "Termination reason: Unknown" line -> Just "Unknown"
        _ -> mStatus
      _ -> mStatus

parseTimeUsed :: [String] -> TimeOfDay
parseTimeUsed = fromMaybe midnight . foldr parseTimeUsedIfTimeLine Nothing
  where
    parseTimeUsedIfTimeLine :: String -> Maybe TimeOfDay -> Maybe TimeOfDay
    parseTimeUsedIfTimeLine line mTime = case mTime of
      Just _ -> mTime
      Nothing -> case stripPrefix "Time elapsed: " line of
        Just s -> Just $ parseTimeOfDay $
          takeWhile (\ c -> isDigit c || c == '.') $ trimLeft s
        Nothing -> mTime

    parseTimeOfDay :: String -> TimeOfDay
    parseTimeOfDay s = TimeOfDay
        { todHour = 0
        , todMin = 0
        , todSec = realToFrac (read s :: Double) }

data FilterState = Version | Separator | Proof deriving Show

-- filters the lines of the proof
-- The first line does not belong to the proof. The next lines before the
-- "------------------------------" belong to the proof.
-- Right after that separator, the version indicator appears.
filterProofLines :: [String] -> [String]
filterProofLines lines = fst $ foldr addIfInProof ([], Version) $ tail lines
  where
    addIfInProof :: String -> ([String], FilterState) -> ([String], FilterState)
    addIfInProof line (addedLines, state) =
      -- @state@ tells if the line is between "SZS output start/end".
      -- Since the lines are in reverse order (by foldr), we need to parse after
      -- the separator ("------------------------------").
      case state of
        Version ->
          if isPrefixOf "Version: " line
          then (addedLines, Separator)
          else (addedLines, state)
        Separator ->
          if isPrefixOf "------------------------------" line
          then (addedLines, Proof)
          else (addedLines, state)
        Proof -> (line : addedLines, state)
