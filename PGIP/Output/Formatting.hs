module PGIP.Output.Formatting where

import Common.Utils

import Logic.Logic
import Logic.Comorphism

import Proofs.AbstractState

import Data.Char

internalProverName :: ProverOrConsChecker -> String
internalProverName pOrCc = case pOrCc of
  Prover pr -> getProverName pr
  ConsChecker cc -> getCcName cc

showComorph :: AnyComorphism -> String
showComorph (Comorphism cid) = mkNiceProverName . drop 1 . dropWhile (/= ':')
  . map (\ c -> if c == ';' then ':' else c)
  $ language_name cid

mkNiceProverName :: String -> String
mkNiceProverName = filter (\ c -> isAlphaNum c || elem c "_.:-")

proversOnly :: [(AnyComorphism, [ProverOrConsChecker])] -> [ProverOrConsChecker]
proversOnly = nubOrdOn (mkNiceProverName . internalProverName) . concatMap snd

showProversOnly :: [(AnyComorphism, [String])] -> [String]
showProversOnly = nubOrd . concatMap snd
