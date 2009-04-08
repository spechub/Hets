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

data FlattenCmd =
    Importing
  | DisjointUnion
  | Renaming
  | Hiding
  | Heterogeneity

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

data GoalKind = AllGoals | ProvenGoals | UnprovenGoals

data InspectCmd =
    CmdList -- all possible commands
  | Libs  -- all imported libraries
  | Nodes -- of library
  | Links
  | UndoHist
  | RedoHist
  | NodeInfo -- of a selected node
  | Theory
  | Goals GoalKind
  | Axioms
  | LocalAxioms
  | Taxonomy
  | Concept
  | LinkInfo -- of a selected link

data Command =
    GlobCommad GlobCmd
  | FlattenCmd FlattenCmd
  | SelectCmd SelectCmd String
  | TimeLimit Int -- set a time limit for an automatic  prover
  | SetAxioms [String] -- set the axiom list for an automatic  prover
  | IncludeProvenTheorems Bool -- should proven theorems be added as axioms
  | InspectCmd InspectCmd
