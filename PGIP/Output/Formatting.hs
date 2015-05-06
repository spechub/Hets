module PGIP.Output.Formatting where

import Common.Utils

import Logic.Logic
import Logic.Comorphism

import PGIP.Common

import Proofs.AbstractState

import Data.Char

proverOrConsCheckerName :: ProverOrConsChecker -> String
proverOrConsCheckerName = removeFunnyChars . internalProverName

internalProverName :: ProverOrConsChecker -> String
internalProverName pOrCc = case pOrCc of
  PGIP.Common.Prover pr -> getProverName pr
  PGIP.Common.ConsChecker cc -> getCcName cc

showComorph :: AnyComorphism -> String
showComorph (Comorphism cid) = removeFunnyChars . drop 1 . dropWhile (/= ':')
  . map (\ c -> if c == ';' then ':' else c)
  $ language_name cid

removeFunnyChars :: String -> String
removeFunnyChars = filter (\ c -> isAlphaNum c || elem c "_.:-")

getWebProverName :: G_prover -> String
getWebProverName = removeFunnyChars . getProverName

proversOnly :: [(AnyComorphism, [ProverOrConsChecker])] -> [ProverOrConsChecker]
proversOnly = nubOrdOn proverOrConsCheckerName . concatMap snd

showProversOnly :: [(AnyComorphism, [String])] -> [String]
showProversOnly = nubOrd . concatMap snd
