{- |
Module      :  $Header$
Description :  development graph commands for all interfaces
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

data types for development graph commands to be invoked via the GUI, the
command-line-interface (CMDL), and other tools
-}

module Interfaces.Command where

data GlobCmd =
    Automatic
  | ThmHideShift
  | HideThmShift
  | GlobDecomp
  | GlobSubsume
  | LocalDecomp
  | LocalInference
  | Composition
  | Colimit
  | NormalForm
  | QualifyNames
  | UndoCmd
  | RedoCmd
    -- Flattening command
  | Importing
  | DisjointUnion
  | Renaming
  | Hiding
  | Heterogeneity
    deriving (Eq, Ord, Enum, Bounded)

globCmdList :: [GlobCmd]
globCmdList = [minBound .. maxBound]

isFlatteningCmd :: GlobCmd -> Bool
isFlatteningCmd c =  c >= Importing

-- | select a named entity
data SelectCmd =
    Lib  -- allows to move to an imported library
  | Node
  | Comorphism
  | Prover
  | Goal  -- a single goal for an automatic prover
  | ConsistencyChecker
  | Link
  | ConservativityChecker
    deriving (Enum, Bounded)

selectCmdList :: [SelectCmd]
selectCmdList = [minBound .. maxBound]

data InspectCmd =
    CmdList -- all possible commands
  | Libs  -- all imported libraries
  | Nodes -- of library
  | Links
  | UndoHist
  | RedoHist
  | NodeInfo -- of a selected node
  | Theory
  | AllGoals
  | ProvenGoals
  | UnprovenGoals
  | Axioms
  | LocalAxioms
  | Taxonomy
  | Concept
  | LinkInfo -- of a selected link
    deriving (Eq, Ord, Enum, Bounded)

inspectCmdList :: [InspectCmd]
inspectCmdList = [minBound .. maxBound]

data Command =
    GlobCmd GlobCmd
  | SelectCmd SelectCmd String
  | TimeLimit Int -- set a time limit for an automatic  prover
  | SetAxioms [String] -- set the axiom list for an automatic  prover
  | IncludeProvenTheorems Bool -- should proven theorems be added as axioms
  | InspectCmd InspectCmd

commandList :: [Command]
commandList =
  map GlobCmd globCmdList
  ++ map (\ s -> SelectCmd s "") selectCmdList
  ++ [TimeLimit (-1), SetAxioms [], IncludeProvenTheorems False]
  ++ map InspectCmd inspectCmdList
