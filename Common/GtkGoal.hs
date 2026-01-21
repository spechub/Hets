module Common.GtkGoal where

import Data.List (isInfixOf)
import Data.Char (toLower)

import Interfaces.GenericATPState

import Logic.Prover

import Static.GTheory

-- * Datatypes and functions for prover

data Goal = Goal
  { gStatus :: GStatus
  , gName :: String }
  deriving (Eq, Ord)

toGtkGoal :: (String, Maybe BasicProof) -> Goal
toGtkGoal (n, st) =
          Goal { gName = n
               , gStatus = maybe GOpen basicProofToGStatus st }

showGoal :: Goal -> String
showGoal (Goal { gName = n, gStatus = s }) =
  spanString s $ statusToPrefix s ++ n

data GStatus = GOpen
             | GTimeout
             | GDisproved
             | GInconsistent
             | GProved
             | GGuessed
             | GConjectured
             | GHandwritten
               deriving (Eq, Ord)

instance Show GStatus where
  show GProved = spanString GProved "Proved"
  show GInconsistent = spanString GInconsistent "Inconsistent"
  show GDisproved = spanString GDisproved "Disproved"
  show GOpen = spanString GOpen "Open"
  show GTimeout = spanString GTimeout "Open (Timeout!)"
  show GGuessed = spanString GGuessed "Guessed"
  show GConjectured = spanString GConjectured "Conjectured"
  show GHandwritten = spanString GHandwritten "Handwritten"

showSimple :: GStatus -> String
showSimple gs = case gs of
  GProved -> "Proved"
  GInconsistent -> "Inconsistent"
  GDisproved -> "Disproved"
  GOpen -> "Open"
  GTimeout -> "Open (Timeout!)"
  GGuessed -> "Guessed"
  GConjectured -> "Conjectured"
  GHandwritten -> "Handwritten"


statusToColor :: GStatus -> String
statusToColor s = case s of
  GOpen -> "black"
  GProved -> "green"
  GDisproved -> "red"
  GTimeout -> "blue"
  GInconsistent -> "orange"
  GGuessed -> "darkgreen"
  GConjectured -> "darkgreen"
  GHandwritten -> "darkgreen"

statusToPrefix :: GStatus -> String
statusToPrefix s = case s of
  GOpen -> "[ ] "
  GProved -> "[+] "
  GDisproved -> "[-] "
  GTimeout -> "[t] "
  GInconsistent -> "[*] "
  GGuessed -> "[.] "
  GConjectured -> "[:] "
  GHandwritten -> "[/] "

spanString :: GStatus -> String -> String
spanString s m = "<span color=\"" ++ statusToColor s ++ "\">" ++ m ++ "</span>"

-- | Converts a ProofStatus into a GStatus
proofStatusToGStatus :: ProofStatus a -> GStatus
proofStatusToGStatus p = case goalStatus p of
  Proved False -> GInconsistent
  Proved True -> GProved
  Disproved -> GDisproved
  Open reason ->
    if any (isInfixOf "timeout" . map toLower) reason then GTimeout else GOpen

-- | Converts a BasicProof into a GStatus
basicProofToGStatus :: BasicProof -> GStatus
basicProofToGStatus p = case p of
  BasicProof _ st -> proofStatusToGStatus st
  Guessed -> GGuessed
  Conjectured -> GConjectured
  Handwritten -> GHandwritten

-- | Converts a GenericConfig into a GStatus
genericConfigToGStatus :: GenericConfig a -> GStatus
genericConfigToGStatus cfg = case proofStatusToGStatus $ proofStatus cfg of
  GOpen -> if timeLimitExceeded cfg then GTimeout else GOpen
  s -> s
