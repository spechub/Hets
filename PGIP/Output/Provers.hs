{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.Output.Provers
  ( formatProvers
  , prepareFormatProver
  , Prover
  , mkProver
  ) where

import PGIP.Output.Formatting
import PGIP.Output.Mime

import PGIP.Shared (ProverMode (..))

import Logic.Comorphism (AnyComorphism)

import Proofs.AbstractState (ProverOrConsChecker)

import Common.Json (ppJson, asJson)
import Common.ToXml (asXml)

import Text.XML.Light (ppTopElement)

import Data.Data

type ProversFormatter = ProverMode
                        -> [(AnyComorphism, [ProverOrConsChecker])]
                        -> (String, String)

formatProvers :: Maybe String -> ProversFormatter
formatProvers format proverMode availableProvers = case format of
  Just "json" -> formatAsJSON
  _ -> formatAsXML
  where
  computedProvers :: Provers
  computedProvers =
    let proverNames = map prepareFormatProver $ proversOnly availableProvers
    in case proverMode of
      GlProofs -> emptyProvers { provers = Just proverNames }
      GlConsistency -> emptyProvers { consistencyCheckers = Just proverNames }

  formatAsJSON :: (String, String)
  formatAsJSON = (jsonC, ppJson $ asJson computedProvers)

  formatAsXML :: (String, String)
  formatAsXML = (xmlC, ppTopElement $ asXml computedProvers)

prepareFormatProver :: ProverOrConsChecker -> Prover
prepareFormatProver = mkProver . internalProverName

data Provers = Provers
  { provers :: Maybe [Prover]
  , consistencyCheckers :: Maybe [Prover]
  } deriving (Show, Typeable, Data)

data Prover = Prover
  { identifier :: String
  , name :: String
  } deriving (Show, Typeable, Data)

emptyProvers :: Provers
emptyProvers = Provers { provers = Nothing, consistencyCheckers = Nothing }

mkProver :: String -> Prover
mkProver s = Prover { name = s, identifier = mkNiceProverName s }
