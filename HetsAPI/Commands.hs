module HetsAPI.Commands (
   automatic
   , globalSubsume
   , globalDecomposition
   , localInference
   , localDecomposition
   , compositionProveEdges
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
   , getGraphForLibrary
   , getNodesFromDevelopmentGraph
   , getLNodesFromDevelopmentGraph
   , translateTheory
   , showTheory

   -- Hets.ProveCommands
   , HPC.availableComorphisms
   , HPC.usableProvers
   , HPC.usableConsistencyCheckers
   , HPC.autoProveNode
   , HPC.proveNode
   , HPC.checkConsistency
   , HPC.checkConservativityNode 
) where

import qualified Data.Map as Map
import Data.Graph.Inductive.Graph (LNode)

import Control.Monad.Trans (lift)

import Common.Result (Result(..), fatal_error, maybeToResult, justHint)
import Common.Id(nullRange)
import Common.LibName (LibName)
import Common.ResultT (runResultT, liftR)

import Interfaces.CmdAction (globLibAct, globLibResultAct)
import Interfaces.Command (GlobCmd(..), SelectCmd (Lib))

import qualified HetsAPI.ProveCommands as HPC

import Driver.AnaLib (anaLib)
import Driver.Options (HetcatsOpts)

import Logic.Comorphism (AnyComorphism)
import Static.DevGraph (LibEnv, DGraph, lookupDGraph, DGNodeLab, labNodesDG)
import Static.GTheory (G_theory, mapG_theory)
import Common.DocUtils (Pretty(pretty))


err :: String -> Result a
err s = fatal_error s nullRange

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

-- | @getDevelopmentGraphByName name env@ returns the development graph for the
--   library @name@ in the environment @env@.
getGraphForLibrary :: LibName -> LibEnv -> DGraph
getGraphForLibrary = lookupDGraph

-- | @getNodesFromDevelopmentGraph graph@ returns the nodes of the development
--   graph @graph@
getNodesFromDevelopmentGraph :: DGraph -> [DGNodeLab]
getNodesFromDevelopmentGraph = fmap snd . labNodesDG


-- | @getNodesFromDevelopmentGraph graph@ returns the nodes of the development
--   graph @graph@
getLNodesFromDevelopmentGraph :: DGraph -> [LNode DGNodeLab]
getLNodesFromDevelopmentGraph = labNodesDG

translateTheory :: AnyComorphism -> G_theory -> Result G_theory
translateTheory = mapG_theory False

showTheory :: G_theory -> String
showTheory = show . pretty








