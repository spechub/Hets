module HetsState.Api (
  HetsState,
  dgAllAuto,
  dgAllGlobalDecomposition,
  dgAllGlobalSubsume,
  dgAllLocalDecomposition,
  dgAllLocalInference,
  dgAllCompositionProveEdges,
  dgAllCompNew,
  dgAllCons,
  dgAllHideThm,
  dgAllThmHide,
  computeColimit,
  computeNormalForm,
  triangleCons,
  freeness,
  flatteningImporting,
  flatteningDisjointUnion,
  flatteningRenaming,
  flatteningHiding,
  flatteningHeterogeneity,
  qualifyAllNames,
  undo,
  redo,
  showOutputFalse,
  showOutputTrue,
  use,
  dgBasic,
  translate,
  prover,
  setGoals,
  prove,
  disprove,
  checkConsistency,
  globallyCheckConservativity,
  dropTranslations,
  consChecker,
  conservativityCheckOpen,
  conservativityCheck,
  setTimeLimit,
  setAxioms,
  setIncludeTheoremsTrue,
  setIncludeTheoremsFalse,
  nodes,
  edges,
  showUndoHistory,
  showRedoHistory,
  showCurrentComorphism,
  showProvenGoalsCurrent,
  showUnprovenGoalsCurrent,
  showAllAxiomsCurrent,
  showAllGoalsCurrent,
  showComputedTheoryCurrent,
  showTranslatedTheoryCurrent,
  showTaxonomyCurrent,
  showConceptCurrent,
  showNodeInfoCurrent,
  showComorphismsTo,
  showNodeInfo,
  showComputedTheory,
  showTranslatedTheory,
  showAllGoals,
  showProvenGoals,
  showUnprovenGoals,
  showAllAxioms,
  showTaxonomy,
  showConcept,
  showEdgeInfo,
  addview,
  expand
) where

import qualified Interfaces.DataTypes as I
import Interfaces.History (add2history)
import Interfaces.Utils (emptyIntIState)
import Interfaces.Command (Command (..))

import Driver.Options (HetcatsOpts)

import Common.Result (Result (..), fatal_error)
import Common.LibName (LibName)
import Common.Id (nullRange)

import Static.DevGraph (LibEnv)

import qualified Hets.Proofs as Proofs


data HetsState = HetsState {
    intState :: I.IntState -- ^ common interface state
  , hetsOpts :: HetcatsOpts  -- ^ hets command options
}

err :: String -> Result a
err s = fatal_error s nullRange

add2hist :: [I.UndoRedoElem] -> HetsState -> HetsState
add2hist descr hets = let intst = add2history (CommentCmd "") (intState st) descr
   in hets { intState = intst }

-- | General function for implementing dg all style commands
commandDgAll :: (LibName -> LibEnv -> Result LibEnv)
             -> HetsState -> Result HetsState
commandDgAll fn state = case I.i_state $ intState state of
  Nothing ->  error "No library loaded"
  Just ist -> case fn (I.i_ln ist) (I.i_libEnv ist) of
    Result _ (Just nwLibEnv) ->
         {- Name of function is not known here, so an empty text is
         added as name, in a later stage (Shell.hs) the name will
         be inserted -}
        return $ add2hist [I.IStateChange $ Just ist] $ state
             { intState = (intState state)
                 { I.i_state = Just $ emptyIntIState nwLibEnv $ I.i_ln ist } }
    Result diag Nothing -> Result diag Nothing

asResult :: (a -> b -> c) -> a -> b -> Result c
asResult fn a b = return $ fn a b

dgAllAuto :: HetsState -> Result HetsState
dgAllAuto = commandDgAll (asResult Proofs.automatic)

dgAllGlobalDecomposition :: HetsState -> Result HetsState
dgAllGlobalDecomposition = commandDgAll (asResult Proofs.globalDecomposition)

dgAllGlobalSubsume :: HetsState -> Result HetsState
dgAllGlobalSubsume = commandDgAll (asResult Proofs.globalSubsume)

dgAllLocalDecomposition :: HetsState -> Result HetsState
dgAllLocalDecomposition = commandDgAll (asResult Proofs.localDecomposition)

dgAllLocalInference :: HetsState -> Result HetsState
dgAllLocalInference = commandDgAll (asResult Proofs.localInference)

dgAllCompositionProveEdges :: HetsState -> Result HetsState
dgAllCompositionProveEdges = commandDgAll (asResult Proofs.allCom)

dgAllCompNew :: HetsState -> Result HetsState
dgAllCompNew = return

dgAllCons :: HetsState -> Result HetsState
dgAllCons = return

dgAllHideThm :: HetsState -> Result HetsState
dgAllHideThm = return

dgAllThmHide :: HetsState -> Result HetsState
dgAllThmHide = return

computeColimit :: HetsState -> Result HetsState
computeColimit = return

computeNormalForm :: HetsState -> Result HetsState
computeNormalForm = return

triangleCons :: HetsState -> Result HetsState
triangleCons = return

freeness :: HetsState -> Result HetsState
freeness = return

flatteningImporting :: HetsState -> Result HetsState
flatteningImporting = return

flatteningDisjointUnion :: HetsState -> Result HetsState
flatteningDisjointUnion = return

flatteningRenaming :: HetsState -> Result HetsState
flatteningRenaming = return

flatteningHiding :: HetsState -> Result HetsState
flatteningHiding = return

flatteningHeterogeneity :: HetsState -> Result HetsState
flatteningHeterogeneity = return

qualifyAllNames :: HetsState -> Result HetsState
qualifyAllNames = return

undo :: HetsState -> Result HetsState
undo = return

redo :: HetsState -> Result HetsState
redo = return

showOutputFalse :: HetsState -> Result HetsState
showOutputFalse = return

showOutputTrue :: HetsState -> Result HetsState
showOutputTrue = return

use :: HetsState -> Result HetsState
use hets file = return hets

dgBasic :: HetsState -> Result HetsState
dgBasic hets nodes = return hets

translate :: HetsState -> String -> Result HetsState
translate hets comorphism = return hets

prover :: HetsState -> String -> Result HetsState
prover hets prover = return hets

setGoals :: HetsState -> [String] -> Result HetsState
setGoals hets goals = return hets

prove :: HetsState -> Result HetsState
prove = return

disprove :: HetsState -> Result HetsState
disprove = return

checkConsistency :: HetsState -> Result HetsState
checkConsistency = return

globallyCheckConservativity :: HetsState -> Result HetsState
globallyCheckConservativity = return

dropTranslations :: HetsState -> Result HetsState
dropTranslations = return

consChecker :: HetsState -> String -> Result HetsState
consChecker hets consChecker = return hets

conservativityCheckOpen :: HetsState -> ([String], [String], [String], [String]) -> Result HetsState
conservativityCheckOpen hets openConsNodesOrEdges = return hets

conservativityCheck :: HetsState -> ([String], [String], [String], [String]) -> Result HetsState
conservativityCheck hets nodesOrEdges = return hets

setTimeLimit :: HetsState -> Int -> Result HetsState
setTimeLimit hets number = return hets

setAxioms :: HetsState -> [String] -> Result HetsState
setAxioms hets axioms = return hets

setIncludeTheoremsTrue :: HetsState -> Result HetsState
setIncludeTheoremsTrue = return

setIncludeTheoremsFalse :: HetsState -> Result HetsState
setIncludeTheoremsFalse = return

nodes :: HetsState -> Result HetsState
nodes = return

edges :: HetsState -> Result HetsState
edges = return

showUndoHistory :: HetsState -> Result HetsState
showUndoHistory = return

showRedoHistory :: HetsState -> Result HetsState
showRedoHistory = return

showCurrentComorphism :: HetsState -> Result HetsState
showCurrentComorphism = return

showProvenGoalsCurrent :: HetsState -> Result HetsState
showProvenGoalsCurrent = return

showUnprovenGoalsCurrent :: HetsState -> Result HetsState
showUnprovenGoalsCurrent = return

showAllAxiomsCurrent :: HetsState -> Result HetsState
showAllAxiomsCurrent = return

showAllGoalsCurrent :: HetsState -> Result HetsState
showAllGoalsCurrent = return

showComputedTheoryCurrent :: HetsState -> Result HetsState
showComputedTheoryCurrent = return

showTranslatedTheoryCurrent :: HetsState -> Result HetsState
showTranslatedTheoryCurrent = return

showTaxonomyCurrent :: HetsState -> Result HetsState
showTaxonomyCurrent = return

showConceptCurrent :: HetsState -> Result HetsState
showConceptCurrent = return

showNodeInfoCurrent :: HetsState -> Result HetsState
showNodeInfoCurrent = return

showComorphismsTo :: HetsState -> Result HetsState
showComorphismsTo hets logic = return hets

showNodeInfo :: HetsState -> Result HetsState
showNodeInfo hets nodes = return hets

showComputedTheory :: HetsState -> [String] -> Result HetsState
showComputedTheory hets nodes = return hets

showTranslatedTheory :: HetsState -> [String] -> Result HetsState
showTranslatedTheory hets nodes = return hets

showAllGoals :: HetsState -> Result HetsState
showAllGoals hets nodes = return hets

showProvenGoals :: HetsState -> Result HetsState
showProvenGoals hets nodes = return hets

showUnprovenGoals :: HetsState -> Result HetsState
showUnprovenGoals hets nodes = return hets

showAllAxioms :: HetsState -> Result HetsState
showAllAxioms hets nodes = return hets

showTaxonomy :: HetsState -> Result HetsState
showTaxonomy hets nodes = return hets

showConcept :: HetsState -> [String] -> Result HetsState
showConcept hets nodes = return hets

showEdgeInfo :: HetsState -> [String] -> Result HetsState
showEdgeInfo hets edges = return hets

expand :: HetsState -> Result HetsState
expand = return

addview :: HetsState -> Result HetsState
addview = return