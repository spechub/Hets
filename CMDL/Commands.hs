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
       , proveAll
       , cmdlIgnoreFunc
       ) where

import Interfaces.Command
import Interfaces.CmdAction (globLibAct, globLibResultAct, globResultAct)

import CMDL.DataTypes
import CMDL.ProveCommands
import CMDL.InfoCommands
import CMDL.DgCommands (cDgSelect, cUse, cExpand, cAddView, commandDgAll,
                        wrapResultDgAll)
import CMDL.ProveConsistency (cConsChecker, cProver)
import CMDL.UndoRedo (cRedo, cUndo)
import CMDL.Shell (cDetails)
import CMDL.ConsCommands (cConservCheck)

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
  genCmd (InspectCmd ic Nothing) CmdNoPriority ReqNothing . CmdNoInput

genInspectCmd :: InspectCmd -> (String -> CmdlState -> IO CmdlState)
              -> CmdlCmdDescription
genInspectCmd ic =
  genCmd (InspectCmd ic (Just "")) CmdNoPriority (reqOfInspectCmd ic)
  . CmdWithInput

genChangeCmd :: ChangeCmd -> (String -> CmdlState -> IO CmdlState)
              -> CmdlCmdDescription
genChangeCmd cc =
  genCmd (mkChangeCmd cc) CmdNoPriority ReqNothing . CmdWithInput

cmdlIgnoreFunc :: String -> CmdlCmdDescription
cmdlIgnoreFunc r =
  genCmd (CommentCmd r) CmdNoPriority ReqNothing $ CmdNoInput return

-- for the synonym "prove-all"
proveAll :: CmdlCmdDescription
proveAll = genGlobCmd ProveCurrent cProve

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
  , proveAll
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
  , genGlobInspectCmd ProvenGoals $ cShowNodeProvenGoals ""
  , genGlobInspectCmd UnprovenGoals $ cShowNodeUnprovenGoals ""
  , genGlobInspectCmd Axioms $ cShowNodeAxioms ""
  , genGlobInspectCmd AllGoals $ cShowTheoryGoals ""
  , genGlobInspectCmd Theory $ cShowTheory Dont_translate ""
  , genGlobInspectCmd Taxonomy $ cShowTaxonomy ""
  , genGlobInspectCmd Concept $ cShowConcept ""
  , genGlobInspectCmd NodeInfo cInfoCurrent
  , genInspectCmd NodeInfo cInfo
  , genInspectCmd Theory $ cShowTheory Dont_translate
  , genInspectCmd AllGoals cShowTheoryGoals
  , genInspectCmd ProvenGoals cShowNodeProvenGoals
  , genInspectCmd UnprovenGoals cShowNodeUnprovenGoals
  , genInspectCmd Axioms cShowNodeAxioms
  , genInspectCmd Taxonomy cShowTaxonomy
  , genInspectCmd Concept cShowConcept
  , genInspectCmd EdgeInfo cInfo ]
  ++
  [ genChangeCmd Expand cExpand
  , genChangeCmd AddView cAddView]
  ++
  [ genCmd HelpCmd CmdNoPriority ReqNothing $ CmdNoInput $ cHelp getCommands
  , genCmd ExitCmd CmdNoPriority ReqNothing $ CmdNoInput return ]