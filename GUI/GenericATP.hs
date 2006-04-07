{- |
Module      :  GenericATP.hs
Description :  Generic Prover GUI.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Rainer Grabbe, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  not yet runnable
Portability :  needs POSIX

Generic GUI for theorem provers. Based upon former SPASS Prover GUI.

-}

{- ToDo:

   - import graphical functions from old SPASS/Prove.hs
   - generalize graphical functions
   
-}

module GUI.GenericATP where


-- some imports maybe necassary for later usage
{-

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Lib.Pretty as Pretty
import Common.PPUtils
import Common.Utils
import qualified Common.Result as Result
import Common.GlobalAnnotations
import qualified Common.Lib.Map as Map
import qualified Common.OrderedMap as OMap

import Data.List
import Data.Maybe
import Data.IORef

import HTk
import Separator
import Space
import XSelection

import GUI.HTkUtils

import Proofs.GUIState
import Logic.Logic
import Logic.Grothendieck
import Logic.Prover
import qualified Comorphisms.KnownProvers as KnownProvers
import qualified Static.DevGraph as DevGraph

-}
import GUI.GenericATPState
