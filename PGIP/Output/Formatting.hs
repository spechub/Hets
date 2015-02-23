module PGIP.Output.Formatting
  ( showComorph
  , getWebProverName
  , removeFunnyChars
  ) where

import Logic.Logic
import Logic.Comorphism

import Proofs.AbstractState

import Data.Char

showComorph :: AnyComorphism -> String
showComorph (Comorphism cid) = removeFunnyChars . drop 1 . dropWhile (/= ':')
  . map (\ c -> if c == ';' then ':' else c)
  $ language_name cid

removeFunnyChars :: String -> String
removeFunnyChars = filter (\ c -> isAlphaNum c || elem c "_.:-")

getWebProverName :: G_prover -> String
getWebProverName = removeFunnyChars . getProverName
