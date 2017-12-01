{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.Output.Proof
  ( ProofFormatterOptions
  , proofFormatterOptions
  , pfoIncludeProof
  , pfoIncludeDetails

  , ProofResult
  , formatProofs
  ) where

import PGIP.Output.Formatting
import PGIP.Output.Mime
import PGIP.Output.Provers (Prover, prepareFormatProver)

import Interfaces.GenericATPState (tsTimeLimit, tsExtraOpts)
import Logic.Comorphism (AnyComorphism)

import qualified Logic.Prover as LP

import Proofs.AbstractState (G_proof_tree, ProverOrConsChecker)

import Common.Json (ppJson, asJson)
import Common.ToXml (asXml)
import Common.Utils (readMaybe)

import Data.Data
import Data.Time.LocalTime

import Numeric

import Text.XML.Light (ppTopElement)
import Text.Printf (printf)

type ProofResult = (String, String, String, ProverOrConsChecker,
                -- (goalName, goalResult, goalDetails, prover,
                    AnyComorphism, Maybe (LP.ProofStatus G_proof_tree))
                -- translation, proofStatusM)
type ProofFormatter =
    ProofFormatterOptions -> [(String, [ProofResult])] -> (String, String)
                          -- [(dgNodeName, result)]  -> (responseType, response)

data ProofFormatterOptions = ProofFormatterOptions
  { pfoIncludeProof :: Bool
  , pfoIncludeDetails :: Bool
  } deriving (Show, Eq)

proofFormatterOptions :: ProofFormatterOptions
proofFormatterOptions = ProofFormatterOptions
  { pfoIncludeProof = True
  , pfoIncludeDetails = True
  }

formatProofs :: Maybe String -> ProofFormatter
formatProofs format options proofs = case format of
  Just "json" -> formatAsJSON
  _ -> formatAsXML
  where
  proof :: [Proof]
  proof = map convertProof proofs

  formatAsJSON :: (String, String)
  formatAsJSON = (jsonC, ppJson $ asJson proof)

  formatAsXML :: (String, String)
  formatAsXML = (xmlC, ppTopElement $ asXml proof)

  convertProof :: (String, [ProofResult]) -> Proof
  convertProof (nodeName, proofResults) = Proof
    { node = nodeName
    , goals = map convertGoal proofResults
    }

  convertGoal :: ProofResult -> ProofGoal
  convertGoal (goalName, goalResult, goalDetails, proverOrConsChecker,
               translation, proofStatusM) =
    ProofGoal
      { name = goalName
      , result = goalResult
      , details =
          if pfoIncludeDetails options
          then Just goalDetails
          else Nothing
      , usedProver = prepareFormatProver proverOrConsChecker
      , usedTranslation = showComorph translation
      , tacticScript = convertTacticScript proofStatusM
      , proofTree = fmap (show . LP.proofTree) proofStatusM
      , usedTime = fmap (convertTime . LP.usedTime) proofStatusM
      , usedAxioms = fmap LP.usedAxioms proofStatusM
      , proverOutput =
          if pfoIncludeProof options
          then fmap (unlines . LP.proofLines) proofStatusM
          else Nothing
      }

  convertTime :: TimeOfDay -> ProofTime
  convertTime tod = ProofTime
    { seconds = printf "%.3f" (read $ init $ show $ timeOfDayToTime tod :: Double)
    , components = convertTimeComponents tod
    }

  convertTimeComponents :: TimeOfDay -> ProofTimeComponents
  convertTimeComponents tod = ProofTimeComponents
    { hours = todHour tod
    , mins = todMin tod
    , secs = case readSigned readFloat $ show $ todSec tod of
        [(n, "")] -> n
        _ -> error $ "Failed reading the number " ++ show (todSec tod)
    }

  convertTacticScript :: Maybe (LP.ProofStatus G_proof_tree)
                      -> Maybe TacticScript
  convertTacticScript Nothing = Nothing
  convertTacticScript (Just ps) =
    case (\ (LP.TacticScript ts) -> readMaybe ts) $ LP.tacticScript ps of
      Nothing -> Nothing
      Just atp -> Just TacticScript { timeLimit = tsTimeLimit atp
                                    , extraOptions = tsExtraOpts atp
                                    }

data Proof = Proof
  { node :: String
  , goals :: [ProofGoal]
  } deriving (Show, Typeable, Data)

data ProofGoal = ProofGoal
  { name :: String
  , result :: String
  , details :: Maybe String
  , usedProver :: Prover
  , usedTranslation :: String
  , tacticScript :: Maybe TacticScript
  , proofTree :: Maybe String
  , usedTime :: Maybe ProofTime
  , usedAxioms :: Maybe [String]
  , proverOutput :: Maybe String
  } deriving (Show, Typeable, Data)

data TacticScript = TacticScript
  { timeLimit :: Int
  , extraOptions :: [String]
  } deriving (Show, Typeable, Data)

data ProofTime = ProofTime
  { seconds :: String
  , components :: ProofTimeComponents
  } deriving (Show, Typeable, Data)

data ProofTimeComponents = ProofTimeComponents
  { hours :: Int
  , mins :: Int
  , secs :: Double
  } deriving (Show, Typeable, Data)
