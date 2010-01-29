{- |
Module      :  $Header$
Description :  add to all names in the nodes of the libenv a list of paths
Copyright   :  (c) Ewaryst Schulz DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

the list of all paths by which the name is imported into a node is added
to the name. Additionally we keep the original name.
This pathification is used in the OMDoc facility.
-}

module Proofs.PathifyNames (pathifyLibEnv) where

import Logic.Coerce
import Logic.Comorphism
import Logic.ExtSign
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover

import Static.DevGraph
import Static.GTheory
import Static.History
import Static.ComputeTheory

import Common.DocUtils
import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad

pathifyLibEnv :: LibEnv -> Result LibEnv
pathifyLibEnv libEnv =
    foldM f Map.empty $ getTopsortedLibs libEnv
        where
          f le ln =
              do
                let dg0 = lookupDGraph ln libEnv
                dg <- pathifyDG dg0
                return $ Map.insert ln dg le


pathifyDG :: DGraph -> Result DGraph
pathifyDG dg = do
  foldM pathifyLabNode dg $ topsortedNodes dg


pathifyLabNode :: DGraph -> LNode DGNodeLab -> Result DGraph
pathifyLabNode dg (n, lb) =
   if isDGRef lb then return dg else case dgn_theory lb of
    G_theory lid (ExtSign sig _) x sens y -> do
      (nsig, nsens) <- pathify lid dg n sig sens
      let nlb = lb { dgn_theory = G_theory lid
                     (makeExtSign lid nsig) x
                     nsens y }
      return $ changesDGH dg $ SetNodeLab lb (n, nlb)
