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
       , shellacCommands
       , shellacEvalFunc
       ) where

import System.Console.Shell
import System.Console.Shell.ShellMonad

import Interfaces.Command
import Interfaces.CmdAction

import PGIP.DataTypes
import PGIP.ProveCommands
import PGIP.InfoCommands
import PGIP.DgCommands
import PGIP.ProveConsistency
import PGIP.ConsCommands
import PGIP.Shell
import PGIP.UndoRedo

-- | Generates a shellac command that requires input
shellacWithInput :: CMDL_CmdDescription -> String -> Sh CMDL_State ()
shellacWithInput descr inp =
  shellacCmd descr { cmdDescription = setInputStr inp $ cmdDescription descr }

-- | Generates the list of all the shell commands together
-- with a short description
shellacCommands :: [ShellCommand CMDL_State]
shellacCommands
 = let genCmds = concatMap (\x ->
              map (\y-> case cmdFn x of
                         CmdNoInput _ -> cmd y (shellacCmd x)
                            $ describeCmd $ cmdDescription x
                         CmdWithInput _ -> cmd y (shellacWithInput x)
                            $ describeCmd $ cmdDescription x
                             ) [cmdName x]) getCommands
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
genCmd :: Command -> CMDL_CmdPriority ->
          CMDL_CmdRequirements -> CMDL_CmdFnClasses ->
          CMDL_CmdDescription
genCmd c priority req fn = CMDL_CmdDescription
  { cmdDescription = c
  , cmdPriority = priority
  , cmdReq = req
  , cmdFn = fn }

genGlobCmd :: GlobCmd -> (CMDL_State -> IO CMDL_State) -> CMDL_CmdDescription
genGlobCmd gc cf =
  genCmd (GlobCmd gc) CmdNoPriority ReqNothing $ CmdNoInput cf

reqOfSelectCmd :: SelectCmd -> CMDL_CmdRequirements
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

genSelectCmd :: SelectCmd -> (String -> CMDL_State -> IO CMDL_State)
             -> CMDL_CmdDescription
genSelectCmd sc cf =
  genCmd (mkSelectCmd sc) CmdNoPriority (reqOfSelectCmd sc) $ CmdWithInput cf

reqOfInspectCmd :: InspectCmd -> CMDL_CmdRequirements
reqOfInspectCmd ic = case ic of
  EdgeInfo -> ReqEdges
  _ -> if requiresNode ic then ReqNodes else ReqNothing

genGlobInspectCmd :: InspectCmd -> (CMDL_State -> IO CMDL_State)
                  -> CMDL_CmdDescription
genGlobInspectCmd ic cf =
  genCmd (InspectCmd ic) CmdNoPriority ReqNothing $ CmdNoInput cf

genInspectCmd :: InspectCmd -> (String -> CMDL_State -> IO CMDL_State)
              -> CMDL_CmdDescription
genInspectCmd ic cf =
  genCmd (InspectCmd ic) CmdNoPriority (reqOfInspectCmd ic) $ CmdWithInput cf

-- | Evaluation function description (function called when input can not
-- be parsed
cmdlEvalFunc :: CMDL_CmdDescription
cmdlEvalFunc =
  genCmd (CommentCmd "") CmdNoPriority ReqNothing $ CmdWithInput cNotACommand

-- | Shellac description of the evaluation function
shellacEvalFunc :: String -> Sh CMDL_State ()
shellacEvalFunc input = shellacWithInput cmdlEvalFunc input

-- | Generates the list of all possible commands as command description
getCommands :: [CMDL_CmdDescription]
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
  , genSelectCmd Prover $ cProver
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
  , genGlobInspectCmd RedoHist cUndoHistory
  , genInspectCmd NodeInfo cInfo
  , genInspectCmd Theory $ cShowTheory Dont_translate
  , genInspectCmd AllGoals cShowTheoryGoals
  , genInspectCmd ProvenGoals cShowNodePGoals
  , genInspectCmd UnprovenGoals cShowNodeUGoals
  , genInspectCmd Axioms cShowNodeAxioms
  , genInspectCmd Taxonomy cShowTaxonomy
  , genInspectCmd Concept cShowConcept
  , genInspectCmd EdgeInfo cInfo ]
