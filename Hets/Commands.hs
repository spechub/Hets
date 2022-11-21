module Hets.Commands where

import qualified Data.Map as Map

import Control.Monad.Trans

import Common.Result (Result(..), fatal_error, maybeToResult, justHint)
import Common.Id(nullRange)
import Common.LibName (LibName)
import Common.ResultT

import Interfaces.CmdAction
import Interfaces.Command (GlobCmd(..), SelectCmd (Lib))


import Driver.AnaLib (anaLib)
import Driver.Options (HetcatsOpts)

import Static.DevGraph (LibEnv)

import Hets.ProveCommand

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


loadLibrary :: FilePath -> HetcatsOpts -> ResultT IO (LibName, LibEnv)
loadLibrary file opts = do
   analysisResult <- lift $ anaLib opts file
   case analysisResult of
    Nothing -> liftR $ err ("Unable to load library " ++ file)
    Just lib -> return lib













