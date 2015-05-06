module PGIP.Output.Formatting where

import Common.Utils

import Logic.Logic
import Logic.Comorphism

import Proofs.AbstractState

import Data.Char

proverOrConsCheckerName :: ProverOrConsChecker -> String
proverOrConsCheckerName = mkNiceProverName . internalProverName

internalProverName :: ProverOrConsChecker -> String
internalProverName pOrCc = case pOrCc of
  Proofs.AbstractState.Prover pr -> getProverName pr
  Proofs.AbstractState.ConsChecker cc -> getCcName cc

showComorph :: AnyComorphism -> String
showComorph (Comorphism cid) = mkNiceProverName . drop 1 . dropWhile (/= ':')
  . map (\ c -> if c == ';' then ':' else c)
  $ language_name cid

mkNiceProverName :: String -> String
mkNiceProverName = filter (\ c -> isAlphaNum c || elem c "_.:-")

getWebProverName :: G_prover -> String
getWebProverName = mkNiceProverName . getProverName

proversOnly :: [(AnyComorphism, [ProverOrConsChecker])] -> [ProverOrConsChecker]
proversOnly = nubOrdOn proverOrConsCheckerName . concatMap snd

showProversOnly :: [(AnyComorphism, [String])] -> [String]
showProversOnly = nubOrd . concatMap snd
