{- |
Module      :  ./TPTP/Prover/EProver.hs
Description :  Interface for the E Theorem Prover.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017, Tom Kranz 2021-2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.SPASS.ProofParser (parseOutput) where

import TPTP.Sign

import Common.AS_Annotation
import Common.ProofTree (ProofGraphNode)
import Common.Utils

import Data.Char
import Data.List
import Data.Maybe
import Data.Time (TimeOfDay (..), midnight)

import Text.ParserCombinators.Parsec

parseOutput :: Named Sentence -- ^ the proof goal
            -> [String] -- ^ the SPASS process output
            -> (Maybe String, [String], Bool, TimeOfDay, Bool, [(Int, ProofGraphNode)], [(Int,Int,Int)])
               -- ^ (result, used axioms, output exists, used time, proof exists, proof clauses/inferences, clause/inference relations)
parseOutput namedGoal = foldl parseIt (Nothing, [], False, midnight, False, [], [])
  where
    parseIt :: (Maybe String, [String], Bool, TimeOfDay, Bool, [(Int, ProofGraphNode)], [(Int,Int,Int)])
            -> String
            -> (Maybe String, [String], Bool, TimeOfDay, Bool, [(Int, ProofGraphNode)], [(Int,Int,Int)])
    parseIt (result, axiomsUsed, spass_start_passed, timeUsed, spass_proof_passed, clNodes, clEdges) line =
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
          , spass_proof_passed ||  ("Here is a proof " `isPrefixOf` line)
          , case (spass_proof_passed, parsedProofLine) of
              (True, Right (clId, rule, _, clSntc)) -> [(clId, Right (show clId,clSntc)),(-clId-1,Left rule)]++clNodes
              _ -> clNodes
          , case (spass_proof_passed, parsedProofLine) of
              (True, Right (clId, _, parents, _)) -> [(p, -clId-1, i) | (i,p) <- zip [0..] parents] ++ (-clId-1,clId,-1):clEdges
              _ -> clEdges
          ) where parsedProofLine = runParser proofLine () "" line


proofLine :: Parser (Int, String, [Int], String)
proofLine = do
 clauseId <- decimal
 char '['
 decimal -- What's this?
 char ':'
 rule <- many alphaNum
 optional (char ':')
 parents <- (decimal >>= (\d-> (char '.') >> decimal >> return d)) `sepBy` (char ',')
 string "] "
 clSentence <- many anyChar
 return (clauseId, rule, parents, clSentence) where
   decimal :: Parser Int
   decimal = do
    n <- many1 digit
    return $ read n

parseTimeOfDay :: String -> Maybe TimeOfDay
parseTimeOfDay str =
    case splitOn ':' str of
      [h, m, s] -> Just TimeOfDay
        { todHour = read h
        , todMin = read m
        , todSec = realToFrac (read s :: Double) }
      _ -> Nothing
