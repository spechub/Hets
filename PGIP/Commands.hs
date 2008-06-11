{- |
Module      :$Header$
Description : list of all commands of CMDL interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see Hets/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.Commands contains the description of all commands available
-}

module PGIP.Commands
       ( getCommands
       , cmdlEvalFunc
       , shellacCommands
       , shellacEvalFunc
       ) where

import System.Console.Shell
import System.Console.Shell.ShellMonad


import PGIP.DataTypes
import PGIP.ProveCommands
import PGIP.InfoCommands
import PGIP.DgCommands
import PGIP.ProveConsistency
import PGIP.ConsCommands
import PGIP.Shell
import Proofs.Automatic
import Proofs.Composition
import Proofs.Global
import Proofs.HideTheoremShift
import Proofs.Local
import Proofs.TheoremHideShift
import PGIP.UndoRedo

-- | Generates a shellac command that requires input
shellacWithInput :: CMDL_CmdDescription -> String -> Sh CMDL_State ()
shellacWithInput descr inp
 = let inf = cmdInfo descr
   in shellacCmd descr {cmdInfo = inf {cmdInput = inp} }

-- | Generates the list of all the shell commands toghether
-- with a short description
shellacCommands :: [ShellCommand CMDL_State]
shellacCommands
 = let genCmds = concatMap (\x ->
              map (\y-> case cmdFn x of
                         CmdNoInput _ ->
                           cmd y (shellacCmd x) (cmdDescription x)
                         CmdWithInput _ ->
                           cmd y (shellacWithInput x) (cmdDescription x)
                             )$ cmdNames $ cmdInfo x) getCommands
   in
    -- different names for exit commands
      (exitCommand "exit")
    : (exitCommand "quit")
    -- also vi style
    : (exitCommand ":q")
    -- different name for help commands
    : (helpCommand "help")
    -- also ? for help
    : (helpCommand "?")
    : genCmds


-- | Generates a command description given all parameters
genCmd :: CMDL_CmdType -> [String] -> CMDL_CmdPriority ->
          CMDL_CmdRequirements -> String -> CMDL_CmdFnClasses ->
          CMDL_CmdDescription
genCmd typ name priority req descr fn
 = CMDL_CmdDescription {
      cmdInfo        = CMDL_CmdHistoryDescription {
                           cmdType     = typ,
                           cmdNames     = name,
                           cmdInput    = []
                       },
      cmdPriority    = priority,
      cmdReq         = req,
      cmdFn          = fn,
      cmdDescription = descr
      }

-- | Evaluation function description (function called when input can not
-- be parsed
cmdlEvalFunc :: CMDL_CmdDescription
cmdlEvalFunc
 = genCmd EvalCmd ["eval function"] CmdNoPriority ReqNothing
              "Evaluation function" $ CmdWithInput cNotACommand

-- | Shellac description of the evaluation function
shellacEvalFunc :: String -> Sh CMDL_State ()
shellacEvalFunc input
 = let descr = cmdlEvalFunc
       inf   = cmdInfo descr
   in shellacCmd descr {cmdInfo = inf {cmdInput = input} }

-- | Generates the list of all possible commands as command description
getCommands :: [CMDL_CmdDescription]
getCommands
 =   (genCmd DgCmd ["dg thm-hide"] CmdNoPriority ReqGNodes
             "apply theorem hide shift to a list of nodes" $
             CmdWithInput cDgThmHideShift)
   : (genCmd SystemCmd ["use"] CmdNoPriority ReqFile
             "loads a HetCASL library" $
             CmdWithInput cUse )
   : (genCmd DgCmd ["dg auto"] CmdNoPriority ReqGEdges
             "apply automatic tactic to a list of edges" $
             CmdWithInput $ commandDg automaticFromList)
   : (genCmd DgCmd ["dg glob-subsume"] CmdNoPriority ReqGEdges
             "apply global subsumption to a list of edges" $
             CmdWithInput $ commandDg globSubsumeFromList)
   : (genCmd DgCmd ["dg glob-decomp"] CmdNoPriority ReqGEdges
             "apply global decomposition to a list of edges" $
             CmdWithInput $ commandDg globDecompFromList)
   : (genCmd DgCmd ["dg loc-infer"] CmdNoPriority ReqGEdges
             "apply local inference to a list of edges" $
             CmdWithInput $ commandDg localInferenceFromList)
   : (genCmd DgCmd ["dg loc-decomp"] CmdNoPriority ReqGEdges
             "apply local decomposition to a list of edges" $
             CmdWithInput $ commandDg locDecompFromList)
   : (genCmd DgCmd ["dg comp"] CmdNoPriority ReqGEdges
             "apply composition to a list of edges" $
             CmdWithInput $ commandDg compositionFromList)
   : (genCmd DgCmd ["dg comp-new"] CmdNoPriority ReqGEdges
         "apply composiiton with speculation of new edges to a list of edges"$
             CmdWithInput $ commandDg compositionCreatingEdgesFromList)
   : (genCmd DgCmd ["dg hide-thm"] CmdNoPriority ReqGEdges
              "apply hide theorem shift to a list of edges" $
              CmdWithInput $ commandDg automaticHideTheoremShiftFromList)
   : (genCmd DgCmd ["dg-all auto"] CmdNoPriority ReqNothing
              "apply automatic tactic to all edges" $
              CmdNoInput $ commandDgAll automatic)
   : (genCmd DgCmd ["dg-all glob-subsume"] CmdNoPriority ReqNothing
              "apply global subsumpetion to all edges" $
              CmdNoInput $ commandDgAll globSubsume)
   : (genCmd DgCmd ["dg-all glob-decomp"] CmdNoPriority ReqNothing
              "apply global decomposition to all edges" $
              CmdNoInput $ commandDgAll globDecomp)
   : (genCmd DgCmd ["dg-all loc-infer"] CmdNoPriority ReqNothing
              "apply local inference to all edges" $
              CmdNoInput $ commandDgAll localInference)
   : (genCmd DgCmd ["dg-all loc-decomp"] CmdNoPriority ReqNothing
              "apply local decomposition to all edges" $
              CmdNoInput $ commandDgAll locDecomp)
   : (genCmd DgCmd ["dg-all comp"] CmdNoPriority ReqNothing
              "apply composition to all edges" $
              CmdNoInput $ commandDgAll composition)
   : (genCmd DgCmd ["dg-all comp-new"] CmdNoPriority ReqNothing
              "apply composition with speculation of new edges to all edges"$
              CmdNoInput $ commandDgAll compositionCreatingEdges)
   : (genCmd DgCmd ["dg-all hide-thm"] CmdNoPriority ReqNothing
              "apply hide theorem shift to all edges" $
              CmdNoInput $ commandDgAll automaticHideTheoremShift)
--   : (genCmd DgCmd ["dg-all thm-hide"] CmdNoPriority ReqNothing
--              "apply theorem hide shift to all nodes"$
--              CmdNoInput $ commandDgAll theoremHideShift)
   : (genCmd SelectCmdAll ["select-all","dg-all basic"]
              CmdNoPriority ReqNothing
              "select all nodes for proving" $
              CmdNoInput cDgSelectAll)
   : (genCmd SelectCmd ["select","dg basic"] CmdNoPriority ReqGNodes
               "select a list of nodes for proving "$
              CmdWithInput cDgSelect)
   : (genCmd InfoCmd ["show-undo-history"] CmdNoPriority ReqNothing
              "show the list of action stored for undo" $
              CmdNoInput cUndoHistory)
   : (genCmd InfoCmd ["show-redo-history"] CmdNoPriority ReqNothing
              "show the list of action stored for redo" $
              CmdNoInput cRedoHistory)
   : (genCmd InfoCmd ["show-proven-goals"] CmdNoPriority ReqNodes
              "show the name of proven goals from a list of nodes" $
              CmdWithInput cShowNodePGoals)
   : (genCmd InfoCmd ["show-proven-goals-current"] CmdNoPriority ReqNothing
              "show the name of proven goals from the selected nodes"$
              CmdNoInput cShowNodePGoalsCurrent)
   : (genCmd InfoCmd ["show-unproven-goals"] CmdNoPriority ReqNodes
              "show the name of unproven goals from a list of nodes"$
              CmdWithInput cShowNodeUGoals)
   : (genCmd InfoCmd ["show-unproven-goals-current"] CmdNoPriority ReqNothing
              "show the name of unproven goals from the selected nodes" $
              CmdNoInput cShowNodeUGoalsCurrent)
   : (genCmd InfoCmd ["show-axioms"] CmdNoPriority ReqNodes
              "show the list of axioms contained in the given list of nodes"$
              CmdWithInput cShowNodeAxioms)
   : (genCmd InfoCmd ["show-axioms-current"] CmdNoPriority ReqNothing
              "show the list of axioms contained in the selected nodes" $
              CmdNoInput cShowNodeAxiomsCurrent)
   : (genCmd InfoCmd ["show-dg-goals"] CmdNoPriority ReqNothing
              "show the list of all open dg goals "$
              CmdNoInput cShowDgGoals)
   : (genCmd InfoCmd ["show-theory-goals-current"] CmdNoPriority ReqNothing
              "shows theory of goals from the selected nodes"$
              CmdNoInput cShowTheoryGoalsCurrent)
   : (genCmd InfoCmd ["show-theory-goals"] CmdNoPriority ReqNodes
              "shows list of theory goals"$
              CmdWithInput cShowTheoryGoals)
   : (genCmd InfoCmd ["show-untraslated-theory-current"] CmdNoPriority
              ReqNothing "shows current untranslated theory" $
              CmdNoInput $ (cShowTheoryCurrent Dont_translate) )
   : (genCmd InfoCmd ["show-theory-current"] CmdNoPriority ReqNothing
              "shows current theory and proof goals "$
              CmdNoInput $ cShowTheoryCurrent Do_translate)
   : (genCmd InfoCmd ["show-untranslated-theory"] CmdNoPriority ReqNodes
              "shows untranslated theory of the provided node" $
              CmdWithInput (cShowTheory Dont_translate) )
   : (genCmd InfoCmd ["show-theory"] CmdNoPriority ReqNodes
              "shows theory of the provided node"$
              CmdWithInput (cShowTheory Do_translate) )
   : (genCmd InfoCmd ["info-current"] CmdNoPriority ReqNothing
              "shows info about the selected nodes"$
              CmdNoInput cInfoCurrent )
   : (genCmd InfoCmd ["info"] CmdNoPriority ReqNodesAndEdges
              "shows info about the provided dg node or edge"$
              CmdWithInput cInfo)
   : (genCmd InfoCmd ["show-taxonomy-current"] CmdNoPriority ReqNothing
              "shows taxonomy graph of selected nodes"$
              CmdNoInput cShowTaxonomyCurrent)
   : (genCmd InfoCmd ["show-taxonomy"] CmdNoPriority ReqNodes
              "shows taxonomy graph" $
              CmdWithInput cShowTaxonomy)
   : (genCmd InfoCmd ["show-concept-current"] CmdNoPriority ReqNothing
              "shows concept graph of selected nodes"$
              CmdNoInput cShowConceptCurrent)
   : (genCmd InfoCmd ["show-concept"] CmdNoPriority ReqNodes
              "shows concept graph"$
              CmdWithInput cShowConcept)
   : (genCmd InfoCmd ["node-number"] CmdNoPriority ReqNodes
              "shows node number"$
              CmdWithInput cNodeNumber)
   : (genCmd InfoCmd ["edges"] CmdNoPriority ReqNothing
              "gives a list of all edges in the graph"$
              CmdNoInput cEdges)
   : (genCmd InfoCmd ["nodes"] CmdNoPriority ReqNothing
              "gives a list of all nodes in the graph"$
              CmdNoInput cNodes)
   : (genCmd InfoCmd ["show-graph"] CmdNoPriority ReqNothing
              "displays the current dg graph"$
              CmdNoInput cDisplayGraph)
   : (genCmd ProveCmd ["translate"] CmdNoPriority ReqComorphism
              "translate theory goals along a comorphism"$
              CmdWithInput cTranslate)
   : (genCmd ProveCmd ["prover"] CmdNoPriority ReqProvers
              "selects a prover"$
              CmdWithInput cProver)
   : (genCmd ProveCmd ["set time-limit"] CmdNoPriority ReqNumber
              "Time limit for the prover to run before abortion" $
              CmdWithInput cTimeLimit)
   : (genCmd ProveCmd ["set axioms"] CmdNoPriority ReqAxm
              "Selects what axioms should be used" $
              CmdWithInput $ cGoalsAxmGeneral ActionSet ChangeAxioms)
   : (genCmd ProveCmd ["set-all axioms"] CmdNoPriority ReqNothing
              "Selects all axioms"$
              CmdNoInput $ cGoalsAxmGeneral ActionSetAll ChangeAxioms [])
   : (genCmd ProveCmd ["drop-translations"] CmdNoPriority ReqNothing
              "Drops any selected comorphism" $
              CmdNoInput $ cDropTranslations)
   : (genCmd ProveCmd ["del axioms"] CmdNoPriority ReqAxm
              "Unselects the given axioms"$
              CmdWithInput $ cGoalsAxmGeneral ActionDel ChangeAxioms )
   : (genCmd ProveCmd ["dell-all axioms"] CmdNoPriority ReqNothing
              "Unselects all axioms"$
              CmdNoInput $ cGoalsAxmGeneral ActionDelAll ChangeAxioms [])
   : (genCmd ProveCmd ["add axioms"] CmdNoPriority ReqAxm
              "Adds axioms to the current selections"$
              CmdWithInput $ cGoalsAxmGeneral ActionAdd ChangeAxioms)
   : (genCmd ProveCmd ["set goals"] CmdNoPriority ReqGoal
              "Selects what goals needs to be proven"$
              CmdWithInput $ cGoalsAxmGeneral ActionSet ChangeGoals)
   : (genCmd ProveCmd ["set-all goals"] CmdNoPriority ReqNothing
              "Selects all goals"$
              CmdNoInput $ cGoalsAxmGeneral ActionSetAll ChangeGoals [])
   : (genCmd ProveCmd ["del goals"] CmdNoPriority ReqGoal
              "Unselects the given goals"$
              CmdWithInput $ cGoalsAxmGeneral ActionDel ChangeGoals)
   : (genCmd ProveCmd ["del-all goals"] CmdNoPriority ReqNothing
              "Unselects all axioms"$
              CmdNoInput $ cGoalsAxmGeneral ActionDelAll ChangeGoals [])
   : (genCmd ProveCmd ["add goals"] CmdNoPriority ReqGoal
              "Adds goals to the current selection"$
              CmdWithInput $ cGoalsAxmGeneral ActionAdd ChangeGoals)
   : (genCmd ProveCmd ["set include-theorems true"] CmdNoPriority ReqNothing
              "Include previous proved theorems"$
              CmdNoInput $ cSetUseThms True)
   : (genCmd ProveCmd ["set include-theorems false"] CmdNoPriority ReqNothing
              "Do not include previous proved theorems"$
              CmdNoInput $ cSetUseThms False)
   : (genCmd ProveCmd ["set save-prove-to-file true"] CmdNoPriority ReqNothing
              "Saves the proofs for each goal to a file" $
              CmdNoInput $ cSetSave2File True)
   :(genCmd ProveCmd ["set save-prove-to-file false"] CmdNoPriority ReqNothing
              "Do not save the proofs into files"$
              CmdNoInput $ cSetSave2File False)
   : (genCmd ProveCmd ["begin-script"] CmdNoPriority ReqNothing
              "Prepares the interface for reading a script"$
              CmdNoInput $ cStartScript)
   :(genCmd ProveCmd ["end-script"] CmdGreaterThanScriptAndComments ReqNothing
              "Stops expecting script lines" $
              CmdNoInput $ cEndScript)
   : (genCmd ProveCmd ["prove"] CmdNoPriority ReqNothing
              "Applies a theorem prover to selected goals"$
              CmdNoInput cProve)
   : (genCmd ProveCmd ["prove-all"] CmdNoPriority ReqNothing
              "Applies a theorem prover to all goals" $
              CmdNoInput cProveAll)
   : (genCmd UndoRedoCmd ["undo"] CmdNoPriority ReqNothing
              "Undo last action" $
              CmdNoInput cUndo)
   : (genCmd UndoRedoCmd ["redo"] CmdNoPriority ReqNothing
              "Redo last action "$
              CmdNoInput cRedo)
   : (genCmd SystemCmd ["details"] CmdNoPriority ReqNothing
              "Show list of commands with detailed description"$
              CmdNoInput cDetails)
   : (genCmd SystemCmd ["#","%%"] CmdNoPriority ReqNothing
              "Comment a line"$
              CmdWithInput cComment)
   : (genCmd SystemCmd ["%{"] CmdNoPriority ReqNothing
              "Start a multiple line comment"$
              CmdWithInput cOpenComment)
   : (genCmd SystemCmd ["}%"] CmdGreaterThanComments ReqNothing
              "End a multiple line comment"$
              CmdNoInput cCloseComment)
   : (genCmd ProveCmd ["cons-checker"] CmdNoPriority ReqConsCheck
              "Selects a consistency checker" $
              CmdWithInput cConsChecker)
   : (genCmd InfoCmd ["conservativity-check"] CmdNoPriority ReqEdges
              "Apply conservativity check to a list of edges" $
              CmdWithInput cConservCheck)
   : (genCmd InfoCmd ["conservativity-check-all"] CmdNoPriority ReqNothing
              "Apply conservativity check to all edges" $
              CmdNoInput cConservCheckAll)
   : (genCmd InfoCmd ["consistency-check"] CmdNoPriority ReqNodes
              "Apply consistency check to a list of nodes" $
              CmdWithInput cConsistCheck)
   : (genCmd InfoCmd ["consistency-check-all"] CmdNoPriority ReqNothing
              "Apply consistency check to all nodes" $
               CmdNoInput cConsistCheckAll)
   : []

