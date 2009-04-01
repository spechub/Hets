{- |
Module      :  $Header$
Copyright   :  (c) Ali, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  shabani@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Fact++ prover for OWL
-}

module OWL.ProveFact where

import Logic.Prover

import OWL.Sign
import OWL.Print
import OWL.Sublogic

import GUI.GenericATP
import Interfaces.GenericATPState
import GUI.Utils (createTextSaveDisplay, infoDialog)

import Proofs.BatchProcessing

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.ProofTree
import Common.Result as Result
import Common.Utils

import Data.List (isPrefixOf)
import Data.Time (timeToTimeOfDay)
import Data.Time.Clock (UTCTime(..), secondsToDiffTime, getCurrentTime)

import qualified Control.Concurrent as Concurrent

import System.Exit
import System.IO
import System.Process
import System.Directory

import Control.Monad (when)
import Control.Concurrent
import Control.Concurrent.MVar
