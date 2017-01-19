{- |
Module      :  ./TPTP/Prover/EProver.hs
Description :  Interface for the E Theorem Prover.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.SPASS.ProofParser (parseOutput) where

import TPTP.Sign hiding (InferenceRule)

import Common.AS_Annotation
import Common.Utils

import Data.Char
import Data.List
import Data.Maybe
import Data.Time (TimeOfDay (..), midnight)

parseOutput :: Named Sentence -- ^ the proof goal
            -> [String] -- ^ the SPASS process output
            -> (Maybe String, [String], Bool, TimeOfDay)
               -- ^ (result, used axioms, output exists, used time)
parseOutput namedGoal = foldl parseIt (Nothing, [], False, midnight)
  where
    parseIt :: (Maybe String, [String], Bool, TimeOfDay)
            -> String
            -> (Maybe String, [String], Bool, TimeOfDay)
    parseIt (result, axiomsUsed, spass_start_passed, timeUsed) line =
          ( case stripPrefix "SPASS beiseite: " line of
             r@(Just _) | spass_start_passed -> r
             _ -> result
          , case stripPrefix "Formulae used in the proof :" line of
             Just s -> filter (/= senAttr namedGoal) $ words s
             Nothing -> axiomsUsed
          , spass_start_passed || isInfixOf "SPASS-START" line
          , case stripPrefix "SPASS spent" line of
              Just s | isInfixOf "on the problem." line ->
                fromMaybe midnight $ parseTimeOfDay $
                  takeWhile (\ c -> isDigit c || elem c ".:") $ trimLeft s
              _ -> timeUsed
          )

parseTimeOfDay :: String -> Maybe TimeOfDay
parseTimeOfDay str =
    case splitOn ':' str of
      [h, m, s] -> Just TimeOfDay
        { todHour = read h
        , todMin = read m
        , todSec = realToFrac (read s :: Double) }
      _ -> Nothing
