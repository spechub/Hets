{- |
Module      :$Header$
Description : list of all commands of CMDL interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see Hets/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.Commands contains the description of all commands available
-}

module CMDL.Commands
       ( getCommands
       , shellacCommands
       , shellacEvalFunc
       ) where

import System.Console.Shell(ShellCommand, cmd, exitCommand, helpCommand)
import System.Console.Shell.ShellMonad(Sh)

import Interfaces.Command
import Interfaces.CmdAction(globLibAct, globLibResultAct, globResultAct)

import CMDL.DataTypes
import CMDL.ProveCommands
import CMDL.InfoCommands
import CMDL.DgCommands(cDgSelect, cUse, commandDgAll, wrapResultDgAll)
import CMDL.ProveConsistency(cConsChecker, cProver)
import CMDL.UndoRedo(cRedo, cUndo)
import CMDL.Shell(cDetails, shellacCmd)
import CMDL.ConsCommands(cConservCheck)

-- | Generates a shellac command that requires input
shellacWithInput :: CmdlCmdDescription -> String -> Sh CmdlState ()
shellacWithInput descr inp =
  shellacCmd descr { cmdDescription = setInputStr inp $ cmdDescription descr }

-- | Generates the list of all the shell commands together
-- with a short description
shellacCommands :: [ShellCommand CmdlState]
shellacCommands = let
    genCmds = concatMap (\ x ->
         let desc = cmdDescription x
             cn = cmdName x
         in map (\ y -> (case cmdFn x of
                          CmdNoInput _ -> cmd y $ shellacCmd x
                          CmdWithInput _ -> cmd y $ shellacWithInput x)
                            $ describeCmd desc)
                $ case desc of
                    GlobCmd ProveCurrent -> [cn, "prove-all"]
                    _ -> [cn]) getCommands
    in
    -- different names for exit commands
       map exitCommand ["exit", "quit", ":q"]
    -- different name for help commands
    ++ map helpCommand ["help", "?"]
    ++ genCmds


-- | Generates a command description given all parameters
genCmd :: Command -> CmdlCmdPriority ->
          CmdlCmdRequirements -> CmdlCmdFnClasses ->
          CmdlCmdDescription
genCmd c priority req fn = CmdlCmdDescription
  { cmdDescription = c
  , cmdPriority = priority
  , cmdReq = req
  , cmdFn = fn }

genGlobCmd :: GlobCmd -> (CmdlState -> IO CmdlState) -> CmdlCmdDescription
genGlobCmd gc =
  genCmd (GlobCmd gc) CmdNoPriority ReqNothing . CmdNoInput

reqOfSelectCmd :: SelectCmd -> CmdlCmdRequirements
reqOfSelectCmd sc = case sc of
  LibFile -> ReqFile
  Lib -> ReqFile
  Node -> ReqNodes
  ComorphismTranslation -> ReqComorphism
  Prover -> ReqProvers
  Goal -> ReqGoal
  ConsistencyChecker -> ReqConsCheck
  Link -> ReqEdges
  ConservativityChecker -> ReqEdges

genSelectCmd :: SelectCmd -> (String -> CmdlState -> IO CmdlState)
             -> CmdlCmdDescription
genSelectCmd sc =
  genCmd (mkSelectCmd sc) CmdNoPriority (reqOfSelectCmd sc) . CmdWithInput

reqOfInspectCmd :: InspectCmd -> CmdlCmdRequirements
reqOfInspectCmd ic = case ic of
  EdgeInfo -> ReqEdges
  _ -> if requiresNode ic then ReqNodes else ReqNothing

genGlobInspectCmd :: InspectCmd -> (CmdlState -> IO CmdlState)
                  -> CmdlCmdDescription
genGlobInspectCmd ic =
  genCmd (InspectCmd ic "") CmdNoPriority ReqNothing . CmdNoInput

genInspectCmd :: InspectCmd -> (String -> CmdlState -> IO CmdlState)
              -> CmdlCmdDescription
genInspectCmd ic =
  genCmd (InspectCmd ic "") CmdNoPriority (reqOfInspectCmd ic) . CmdWithInput

-- | Evaluation function description (function called when input can not
-- be parsed
cmdlEvalFunc :: CmdlCmdDescription
cmdlEvalFunc =
  genCmd (CommentCmd "") CmdNoPriority ReqNothing $ CmdWithInput cNotACommand

-- | Shellac description of the evaluation function
shellacEvalFunc :: String -> Sh CmdlState ()
shellacEvalFunc = shellacWithInput cmdlEvalFunc

-- | Generates the list of all possible commands as command description
getCommands :: [CmdlCmdDescription]
getCommands =
  map (\ (cm, act) -> genGlobCmd cm $ commandDgAll $ wrapResultDgAll act)
      globLibAct
  ++ map (\ (cm, act) -> genGlobCmd cm $ commandDgAll act) globLibResultAct
  ++ map (\ (cm, act) -> genGlobCmd cm $ commandDgAll $ const act)
     globResultAct
  ++
  [ genGlobCmd UndoCmd cUndo
  , genGlobCmd RedoCmd cRedo ]
  ++
  [ genSelectCmd LibFile cUse
  , genSelectCmd Node cDgSelect
  , genSelectCmd ComorphismTranslation cTranslate
  , genSelectCmd Prover cProver
  , genSelectCmd Goal $ cGoalsAxmGeneral ActionSet ChangeGoals
  , genGlobCmd ProveCurrent cProve
  , genGlobCmd DropTranslation cDropTranslations
  , genSelectCmd ConsistencyChecker cConsChecker
  , genSelectCmd ConservativityChecker cConservCheck
  , genCmd (TimeLimit 0) CmdNoPriority ReqNumber $ CmdWithInput cTimeLimit
  , genCmd (SetAxioms []) CmdNoPriority ReqAxm $ CmdWithInput
    $ cGoalsAxmGeneral ActionSet ChangeAxioms ]
  ++ map (\ b -> genCmd (IncludeProvenTheorems b) CmdNoPriority ReqNothing
         $ CmdNoInput $ cSetUseThms b) [True, False]
  ++
  [ genGlobInspectCmd CmdList cDetails -- needs to be adjusted
  , genGlobInspectCmd Nodes cNodes
  , genGlobInspectCmd Edges cEdges
  , genGlobInspectCmd UndoHist cUndoHistory
  , genGlobInspectCmd RedoHist cRedoHistory
  , genGlobInspectCmd ProvenGoalsCurrent (cShowNodeProvenGoals "")
  , genGlobInspectCmd UnprovenGoalsCurrent (cShowNodeUnprovenGoals "")
  , genGlobInspectCmd AxiomsCurrent (cShowNodeAxioms "")
  , genGlobInspectCmd AllGoalsCurrent (cShowTheoryGoals "")
  , genGlobInspectCmd TheoryCurrent (cShowTheory Dont_translate "")
  , genGlobInspectCmd TaxonomyCurrent (cShowTaxonomy "")
  , genGlobInspectCmd ConceptCurrent (cShowConcept "")
  , genGlobInspectCmd NodeInfoCurrent cInfoCurrent
  , genInspectCmd NodeInfo cInfo
  , genInspectCmd Theory $ cShowTheory Dont_translate
  , genInspectCmd AllGoals cShowTheoryGoals
  , genInspectCmd ProvenGoals cShowNodeProvenGoals
  , genInspectCmd UnprovenGoals cShowNodeUnprovenGoals
  , genInspectCmd Axioms cShowNodeAxioms
  , genInspectCmd Taxonomy cShowTaxonomy
  , genInspectCmd Concept cShowConcept
  , genInspectCmd EdgeInfo cInfo ]
