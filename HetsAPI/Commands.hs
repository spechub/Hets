{- |
Description :  All commands to interact with the HETS API
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}
module HetsAPI.Commands (
   automatic
   , globalSubsume
   , globalDecomposition
   , localInference
   , localDecomposition
   , compositionProveEdges
   , compositionCreateEdges
   , conservativity
   , automaticHideTheoremShift
   , theoremHideShift
   , computeColimit
   , normalForm
   , triangleCons
   , freeness
   , libFlatImports
   , libFlatDUnions
   , libFlatRenamings
   , libFlatHiding
   , libFlatHeterogen
   , qualifyLibEnv
   , loadLibrary
   , translateTheory
   , showTheory

   -- Hets.ProveCommands
   , HPC.getAvailableComorphisms
   , HPC.getUsableProvers
   , HPC.getUsableConsistencyCheckers
   , HPC.proveNode
   , HPC.asyncProveNode
   , HPC.resultProveNode
   , HPC.abortAsyncProof
   , HPC.checkConsistency
   , HPC.checkConservativityEdge

   -- Hets.InfoCommands
   , HIC.getGraphForLibrary
   , HIC.getNodesFromDevelopmentGraph
   , HIC.getLNodesFromDevelopmentGraph
   , HIC.getAllSentences
   , HIC.getAllAxioms
   , HIC.getAllGoals
   , HIC.getProvenGoals
   , HIC.getUnprovenGoals
) where

import qualified Data.Map as Map


import Common.Result (Result(..))
import Common.LibName (LibName)

import Interfaces.CmdAction (globLibAct, globLibResultAct)
import Interfaces.Command (GlobCmd(..))

import qualified HetsAPI.ProveCommands as HPC
import qualified HetsAPI.InfoCommands as HIC

import Driver.Options (HetcatsOpts)
import Driver.ReadMain (readAndAnalyse)

import Logic.Comorphism (AnyComorphism)
import Static.DevGraph (LibEnv)
import Static.GTheory (G_theory, mapG_theory)
import Common.DocUtils (Pretty(pretty))


globalCommands :: Map.Map GlobCmd (LibName -> LibEnv -> LibEnv)
globalCommands = Map.fromList globLibAct

globalCommand :: GlobCmd -> (LibName -> LibEnv -> LibEnv)
globalCommand = (Map.!) globalCommands

globalCommandsR :: Map.Map GlobCmd (LibName -> LibEnv -> Result LibEnv)
globalCommandsR = Map.fromList globLibResultAct

globalCommandR :: GlobCmd -> (LibName -> LibEnv -> Result LibEnv)
globalCommandR = (Map.!) globalCommandsR



automatic :: LibName -> LibEnv -> LibEnv
automatic = globalCommand Automatic

globalSubsume :: LibName -> LibEnv -> LibEnv
globalSubsume = globalCommand GlobSubsume

globalDecomposition :: LibName -> LibEnv -> LibEnv
globalDecomposition = globalCommand GlobDecomp

localInference :: LibName -> LibEnv -> LibEnv
localInference = globalCommand LocalInference

localDecomposition :: LibName -> LibEnv -> LibEnv
localDecomposition = globalCommand LocalDecomp

compositionProveEdges :: LibName -> LibEnv -> LibEnv
compositionProveEdges = globalCommand CompositionProveEdges

compositionCreateEdges :: LibName -> LibEnv -> LibEnv
compositionCreateEdges = globalCommand CompositionCreateEdges

conservativity :: LibName -> LibEnv -> LibEnv
conservativity = globalCommand Conservativity

automaticHideTheoremShift :: LibName -> LibEnv -> LibEnv
automaticHideTheoremShift = globalCommand HideThmShift


theoremHideShift :: LibName -> LibEnv -> Result LibEnv
theoremHideShift = globalCommandR ThmHideShift

computeColimit :: LibName -> LibEnv -> Result LibEnv
computeColimit = globalCommandR Colimit

normalForm :: LibName -> LibEnv -> Result LibEnv
normalForm = globalCommandR NormalForm

triangleCons :: LibName -> LibEnv -> Result LibEnv
triangleCons = globalCommandR TriangleCons

freeness :: LibName -> LibEnv -> Result LibEnv
freeness = globalCommandR Freeness



libFlatImports :: LibName -> LibEnv -> Result LibEnv
libFlatImports = globalCommandR Importing

libFlatDUnions :: LibName -> LibEnv -> Result LibEnv
libFlatDUnions = globalCommandR DisjointUnion

libFlatRenamings :: LibName -> LibEnv -> Result LibEnv
libFlatRenamings = globalCommandR Renaming

libFlatHiding :: LibName -> LibEnv -> Result LibEnv
libFlatHiding = globalCommandR Hiding

libFlatHeterogen :: LibName -> LibEnv -> Result LibEnv
libFlatHeterogen = globalCommandR Heterogeneity

qualifyLibEnv :: LibName -> LibEnv -> Result LibEnv
qualifyLibEnv = globalCommandR QualifyNames


loadLibrary :: FilePath -> HetcatsOpts -> IO (Result (LibName, LibEnv))
loadLibrary file opts = do
   analysisResult <- readAndAnalyse file opts
   case analysisResult of
    Nothing -> return $ fail  ("Unable to load library " ++ file)
    Just lib -> return $ return lib

translateTheory :: AnyComorphism -> G_theory -> Result G_theory
translateTheory = mapG_theory False

showTheory :: G_theory -> String
showTheory = show . pretty








