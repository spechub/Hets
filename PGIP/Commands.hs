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
import Proofs.TheoremHideShift
import Proofs.Local
import Proofs.ComputeColimit
import Proofs.NormalForm
import Proofs.DGFlattening
import Proofs.QualifyNames
import PGIP.UndoRedo

-- | Generates a shellac command that requires input
shellacWithInput :: CMDL_CmdDescription -> String -> Sh CMDL_State ()
shellacWithInput descr inp
 = shellacCmd descr {cmdInput = inp }

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
                             )$ cmdNames x) getCommands
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
genCmd :: [String] -> CMDL_CmdPriority ->
          CMDL_CmdRequirements -> String -> CMDL_CmdFnClasses ->
          CMDL_CmdDescription
genCmd name priority req descr fn
 = CMDL_CmdDescription {
      cmdNames       = name,
      cmdInput       = [],
      cmdPriority    = priority,
      cmdReq         = req,
      cmdFn          = fn,
      cmdDescription = descr
      }

-- | Evaluation function description (function called when input can not
-- be parsed
cmdlEvalFunc :: CMDL_CmdDescription
cmdlEvalFunc
 = genCmd ["eval function"] CmdNoPriority ReqNothing
              "Evaluation function" $ CmdWithInput cNotACommand

-- | Shellac description of the evaluation function
shellacEvalFunc :: String -> Sh CMDL_State ()
shellacEvalFunc input
 = let descr = cmdlEvalFunc
   in shellacCmd descr {cmdInput = input }

-- | Generates the list of all possible commands as command description
getCommands :: [CMDL_CmdDescription]
getCommands
 =   (genCmd ["dg thm-hide"] CmdNoPriority ReqGNodes
             "apply theorem hide shift to a list of nodes" $
             CmdWithInput cDgThmHideShift)
   : (genCmd ["use"] CmdNoPriority ReqFile
             "loads a HetCASL library" $
             CmdWithInput cUse )
   : (genCmd ["dg auto"] CmdNoPriority ReqGEdges
             "apply automatic tactic to a list of edges" $
             CmdWithInput $ commandDg $ wrapResultDg automaticFromList)
   : (genCmd ["dg glob-subsume"] CmdNoPriority ReqGEdges
             "apply global subsumption to a list of edges" $
             CmdWithInput $ commandDg $ wrapResultDg globSubsumeFromList)
   : (genCmd ["dg glob-decomp"] CmdNoPriority ReqGEdges
             "apply global decomposition to a list of edges" $
             CmdWithInput $ commandDg $ wrapResultDg globDecompFromList)
   : (genCmd ["dg loc-infer"] CmdNoPriority ReqGEdges
             "apply local inference to a list of edges" $
             CmdWithInput $ commandDg $ wrapResultDg localInferenceFromList)
   : (genCmd ["dg loc-decomp"] CmdNoPriority ReqGEdges
             "apply local decomposition to a list of edges" $
             CmdWithInput $ commandDg $wrapResultDg locDecompFromList)
   : (genCmd ["dg comp"] CmdNoPriority ReqGEdges
             "apply composition to a list of edges" $
             CmdWithInput $ commandDg $wrapResultDg compositionFromList)
   : (genCmd ["dg comp-new"] CmdNoPriority ReqGEdges
         "apply composiiton with speculation of new edges to a list of edges"$
             CmdWithInput $ commandDg
                    $ wrapResultDg compositionCreatingEdgesFromList)
   : (genCmd ["dg hide-thm"] CmdNoPriority ReqGEdges
              "apply hide theorem shift to a list of edges" $
              CmdWithInput $ commandDg $
                wrapResultDg automaticHideTheoremShiftFromList)
   : (genCmd ["dg-all auto"] CmdNoPriority ReqNothing
              "apply automatic tactic to all edges" $
              CmdNoInput $ commandDgAll $ wrapResultDgAll automatic)
   : (genCmd ["dg-all glob-subsume"] CmdNoPriority ReqNothing
              "apply global subsumpetion to all edges" $
              CmdNoInput $ commandDgAll $ wrapResultDgAll globSubsume)
   : (genCmd ["dg-all glob-decomp"] CmdNoPriority ReqNothing
              "apply global decomposition to all edges" $
              CmdNoInput $ commandDgAll $ wrapResultDgAll globDecomp)
   : (genCmd ["dg-all loc-infer"] CmdNoPriority ReqNothing
              "apply local inference to all edges" $
              CmdNoInput $ commandDgAll $ wrapResultDgAll localInference)
   : (genCmd ["compute Colimit"] CmdNoPriority ReqNothing
              "computes the colimit" $
              CmdNoInput $ commandDgAll $ computeColimit)
   : (genCmd ["compute normal form"] CmdNoPriority ReqNothing
              "computes normal form" $
              CmdNoInput $ commandDgAll $ normalForm)
   : (genCmd ["flattening importings"] CmdNoPriority ReqNothing
              ("Delete all inclusion links, and insert a new node"++
              " with new computed theory") $ CmdNoInput $ commandDgAll $
              (\_ le -> libEnv_flattening_imports le))
   : (genCmd ["flattening disjoint unions"] CmdNoPriority ReqNothing
             ("For each node with more than two importings modify " ++
             "importings in such a way that at each level only " ++
             " non disjoint signatures are imported") $ CmdNoInput $
             commandDgAll $(\_ le -> libEnv_flattening_dunions le))
   : (genCmd ["flattening renamings"] CmdNoPriority ReqNothing
             ("Determines renaming link, inserts a new node with the " ++
             "renaming morphism applied to theory of a source, deletes "++
             "the link and sets a new inclusion link between a new node "++
             "and the target node") $ CmdNoInput $ commandDgAll $
             (\_ le -> libEnv_flattening_renamings le ))
   : (genCmd ["flattening hiddings"] CmdNoPriority ReqNothing
             ("For each link compute normal form if there is one and "++
             " eliminate hiding links") $ CmdNoInput $ commandDgAll $
             (\_ le -> libEnv_flattening_hiding le))
   : (genCmd ["flattening heterogeneity"] CmdNoPriority ReqNothing
             ("For each heterogeneous link compute theory of a target " ++
             "node and eliminate heterogeneous link") $ CmdNoInput $
             commandDgAll $ (\_ le -> libEnv_flattening_heterogen le))
   : (genCmd ["qualify all names"] CmdNoPriority ReqNothing
             ("Qualify and disambiguate all names in the nodes of the " ++
             "development graph") $ CmdNoInput $ commandDgAll $
             (\_ le -> qualifyLibEnv le))
   : (genCmd ["dg-all loc-decomp"] CmdNoPriority ReqNothing
              "apply local decomposition to all edges" $
              CmdNoInput $ commandDgAll $ wrapResultDgAll locDecomp)
   : (genCmd ["dg-all comp"] CmdNoPriority ReqNothing
              "apply composition to all edges" $
              CmdNoInput $ commandDgAll $ wrapResultDgAll composition)
   : (genCmd ["dg-all comp-new"] CmdNoPriority ReqNothing
              "apply composition with speculation of new edges to all edges"$
              CmdNoInput $ commandDgAll
                         $ wrapResultDgAll compositionCreatingEdges)
   : (genCmd ["dg-all hide-thm"] CmdNoPriority ReqNothing
              "apply hide theorem shift to all edges" $
              CmdNoInput $ commandDgAll
                         $ wrapResultDgAll automaticHideTheoremShift)
   : (genCmd ["dg-all thm-hide"] CmdNoPriority ReqNothing
              "apply theorem hide shift to all nodes"$
              CmdNoInput $ commandDgAll theoremHideShift)
   : (genCmd ["select-all","dg-all basic"]
              CmdNoPriority ReqNothing
              "select all nodes for proving" $
              CmdNoInput cDgSelectAll)
   : (genCmd ["select","dg basic"] CmdNoPriority ReqGNodes
               "select a list of nodes for proving "$
              CmdWithInput cDgSelect)
   : (genCmd ["show-undo-history"] CmdNoPriority ReqNothing
              "show the list of action stored for undo" $
              CmdNoInput cUndoHistory)
   : (genCmd ["show-redo-history"] CmdNoPriority ReqNothing
              "show the list of action stored for redo" $
              CmdNoInput cRedoHistory)
   : (genCmd ["show-proven-goals"] CmdNoPriority ReqNodes
              "show the name of proven goals from a list of nodes" $
              CmdWithInput cShowNodePGoals)
   : (genCmd ["show-proven-goals-current"] CmdNoPriority ReqNothing
              "show the name of proven goals from the selected nodes"$
              CmdNoInput cShowNodePGoalsCurrent)
   : (genCmd ["show-unproven-goals"] CmdNoPriority ReqNodes
              "show the name of unproven goals from a list of nodes"$
              CmdWithInput cShowNodeUGoals)
   : (genCmd ["show-unproven-goals-current"] CmdNoPriority ReqNothing
              "show the name of unproven goals from the selected nodes" $
              CmdNoInput cShowNodeUGoalsCurrent)
   : (genCmd ["show-axioms"] CmdNoPriority ReqNodes
              "show the list of axioms contained in the given list of nodes"$
              CmdWithInput cShowNodeAxioms)
   : (genCmd ["show-axioms-current"] CmdNoPriority ReqNothing
              "show the list of axioms contained in the selected nodes" $
              CmdNoInput cShowNodeAxiomsCurrent)
   : (genCmd ["show-dg-goals"] CmdNoPriority ReqNothing
              "show the list of all open dg goals "$
              CmdNoInput cShowDgGoals)
   : (genCmd ["show-theory-goals-current"] CmdNoPriority ReqNothing
              "shows theory of goals from the selected nodes"$
              CmdNoInput cShowTheoryGoalsCurrent)
   : (genCmd ["show-theory-goals"] CmdNoPriority ReqNodes
              "shows list of theory goals"$
              CmdWithInput cShowTheoryGoals)
   : (genCmd ["show-untranslated-theory-current"] CmdNoPriority
              ReqNothing "shows current untranslated theory" $
              CmdNoInput $ (cShowTheoryCurrent Dont_translate) )
   : (genCmd ["show-theory-current"] CmdNoPriority ReqNothing
              "shows current theory and proof goals "$
              CmdNoInput $ cShowTheoryCurrent Do_translate)
   : (genCmd ["show-untranslated-theory"] CmdNoPriority ReqNodes
              "shows untranslated theory of the provided node" $
              CmdWithInput (cShowTheory Dont_translate) )
   : (genCmd ["show-theory"] CmdNoPriority ReqNodes
              "shows theory of the provided node"$
              CmdWithInput (cShowTheory Do_translate) )
   : (genCmd ["info-current"] CmdNoPriority ReqNothing
              "shows info about the selected nodes"$
              CmdNoInput cInfoCurrent )
   : (genCmd ["info"] CmdNoPriority ReqNodesAndEdges
              "shows info about the provided dg node or edge"$
              CmdWithInput cInfo)
   : (genCmd ["show-taxonomy-current"] CmdNoPriority ReqNothing
              "shows taxonomy graph of selected nodes"$
              CmdNoInput cShowTaxonomyCurrent)
   : (genCmd ["show-taxonomy"] CmdNoPriority ReqNodes
              "shows taxonomy graph" $
              CmdWithInput cShowTaxonomy)
   : (genCmd ["show-concept-current"] CmdNoPriority ReqNothing
              "shows concept graph of selected nodes"$
              CmdNoInput cShowConceptCurrent)
   : (genCmd ["show-concept"] CmdNoPriority ReqNodes
              "shows concept graph"$
              CmdWithInput cShowConcept)
   : (genCmd ["node-number"] CmdNoPriority ReqNodes
              "shows node number"$
              CmdWithInput cNodeNumber)
   : (genCmd ["edges"] CmdNoPriority ReqNothing
              "gives a list of all edges in the graph"$
              CmdNoInput cEdges)
   : (genCmd ["nodes"] CmdNoPriority ReqNothing
              "gives a list of all nodes in the graph"$
              CmdNoInput cNodes)
   : (genCmd ["show-graph"] CmdNoPriority ReqNothing
              "displays the current dg graph"$
              CmdNoInput cDisplayGraph)
   : (genCmd ["translate"] CmdNoPriority ReqComorphism
              "translate theory goals along a comorphism"$
              CmdWithInput cTranslate)
   : (genCmd ["prover"] CmdNoPriority ReqProvers
              "selects a prover"$
              CmdWithInput cProver)
   : (genCmd ["set time-limit"] CmdNoPriority ReqNumber
              "Time limit for the prover to run before abortion" $
              CmdWithInput cTimeLimit)
   : (genCmd ["set axioms"] CmdNoPriority ReqAxm
              "Selects what axioms should be used" $
              CmdWithInput $ cGoalsAxmGeneral ActionSet ChangeAxioms)
   : (genCmd ["set-all axioms"] CmdNoPriority ReqNothing
              "Selects all axioms"$
              CmdNoInput $ cGoalsAxmGeneral ActionSetAll ChangeAxioms [])
   : (genCmd ["drop-translations"] CmdNoPriority ReqNothing
              "Drops any selected comorphism" $
              CmdNoInput $ cDropTranslations)
   : (genCmd ["del axioms"] CmdNoPriority ReqAxm
              "Unselects the given axioms"$
              CmdWithInput $ cGoalsAxmGeneral ActionDel ChangeAxioms )
   : (genCmd ["dell-all axioms"] CmdNoPriority ReqNothing
              "Unselects all axioms"$
              CmdNoInput $ cGoalsAxmGeneral ActionDelAll ChangeAxioms [])
   : (genCmd ["add axioms"] CmdNoPriority ReqAxm
              "Adds axioms to the current selections"$
              CmdWithInput $ cGoalsAxmGeneral ActionAdd ChangeAxioms)
   : (genCmd ["set goals"] CmdNoPriority ReqGoal
              "Selects what goals needs to be proven"$
              CmdWithInput $ cGoalsAxmGeneral ActionSet ChangeGoals)
   : (genCmd ["set-all goals"] CmdNoPriority ReqNothing
              "Selects all goals"$
              CmdNoInput $ cGoalsAxmGeneral ActionSetAll ChangeGoals [])
   : (genCmd ["del goals"] CmdNoPriority ReqGoal
              "Unselects the given goals"$
              CmdWithInput $ cGoalsAxmGeneral ActionDel ChangeGoals)
   : (genCmd ["del-all goals"] CmdNoPriority ReqNothing
              "Unselects all axioms"$
              CmdNoInput $ cGoalsAxmGeneral ActionDelAll ChangeGoals [])
   : (genCmd ["add goals"] CmdNoPriority ReqGoal
              "Adds goals to the current selection"$
              CmdWithInput $ cGoalsAxmGeneral ActionAdd ChangeGoals)
   : (genCmd ["set include-theorems true"] CmdNoPriority ReqNothing
              "Include previous proved theorems"$
              CmdNoInput $ cSetUseThms True)
   : (genCmd ["set include-theorems false"] CmdNoPriority ReqNothing
              "Do not include previous proved theorems"$
              CmdNoInput $ cSetUseThms False)
   : (genCmd ["set save-prove-to-file true"] CmdNoPriority ReqNothing
              "Saves the proofs for each goal to a file" $
              CmdNoInput $ cSetSave2File True)
   : (genCmd ["set save-prove-to-file false"] CmdNoPriority ReqNothing
              "Do not save the proofs into files"$
              CmdNoInput $ cSetSave2File False)
   : (genCmd ["begin-script"] CmdNoPriority ReqNothing
              "Prepares the interface for reading a script"$
              CmdNoInput $ cStartScript)
   : (genCmd ["end-script"] CmdGreaterThanScriptAndComments ReqNothing
              "Stops expecting script lines" $
              CmdNoInput $ cEndScript)
   : (genCmd ["prove"] CmdNoPriority ReqNothing
              "Applies a theorem prover to selected goals"$
              CmdNoInput cProve)
   : (genCmd ["prove-all"] CmdNoPriority ReqNothing
              "Applies a theorem prover to all goals" $
              CmdNoInput cProveAll)
   : (genCmd ["undo"] CmdNoPriority ReqNothing
              "Undo last action" $
              CmdNoInput cUndo)
   : (genCmd ["redo"] CmdNoPriority ReqNothing
              "Redo last action "$
              CmdNoInput cRedo)
   : (genCmd ["details"] CmdNoPriority ReqNothing
              "Show list of commands with detailed description"$
              CmdNoInput cDetails)
   : (genCmd ["#","%%"] CmdNoPriority ReqNothing
              "Comment a line"$
              CmdWithInput cComment)
   : (genCmd ["%{"] CmdNoPriority ReqNothing
              "Start a multiple line comment"$
              CmdWithInput cOpenComment)
   : (genCmd ["}%"] CmdGreaterThanComments ReqNothing
              "End a multiple line comment"$
              CmdNoInput cCloseComment)
   : (genCmd ["cons-checker"] CmdNoPriority ReqConsCheck
              "Selects a consistency checker" $
              CmdWithInput cConsChecker)
   : (genCmd ["conservativity-check"] CmdNoPriority ReqEdges
              "Apply conservativity check to a list of edges" $
              CmdWithInput cConservCheck)
   : (genCmd ["conservativity-check-all"] CmdNoPriority ReqNothing
              "Apply conservativity check to all edges" $
              CmdNoInput cConservCheckAll)
   : (genCmd ["consistency-check"] CmdNoPriority ReqNodes
              "Apply consistency check to a list of nodes" $
              CmdNoInput cConsistCheck)
   : (genCmd ["consistency-check-all"] CmdNoPriority ReqNothing
              "Apply consistency check to all nodes" $
               CmdNoInput cConsistCheckAll)
   : []
