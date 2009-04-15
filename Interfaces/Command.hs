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

import Data.Char

data GlobCmd =
    Automatic
  | ThmHideShift
  | HideThmShift
  | GlobDecomp
  | GlobSubsume
  | LocalDecomp
  | LocalInference
  | Composition
  | CompositionCreateEdges
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

menuTextGlobCmd :: GlobCmd -> String
menuTextGlobCmd cmd = case cmd of
  Automatic -> "Automatic"
  ThmHideShift -> "Theorem-Hide-Shift"
  HideThmShift -> "Hide-Theorem-Shift"
  GlobDecomp -> "Global-Decomposition"
  GlobSubsume -> "Global-Subsumption"
  LocalDecomp -> "Local-Decomposition"
  LocalInference -> "Local-Inference"
  Composition -> "Proof composed edges"
  CompositionCreateEdges -> "Create composed proven edges"
  Colimit -> "Compute colimit"
  NormalForm -> "Compute normal form"
  QualifyNames -> "Qualify all names"
  UndoCmd -> "Undo"
  RedoCmd -> "Redo"
  Importing -> "Importings"
  DisjointUnion -> "Disjoint union"
  Renaming -> "Renamings"
  Hiding -> "Hiding"
  Heterogeneity -> "Heterogeneity"

isDgRule :: GlobCmd -> Bool
isDgRule c = c <= LocalInference

isFlatteningCmd :: GlobCmd -> Bool
isFlatteningCmd c = c >= Importing

isUndoOrRedo :: GlobCmd -> Bool
isUndoOrRedo c = elem c [UndoCmd, RedoCmd]

describeGlobCmd :: GlobCmd -> String
describeGlobCmd c = let t = map toLower $ menuTextGlobCmd c in
  if isDgRule c then "dg rule " ++ t
  else if isFlatteningCmd c then "flattening out " ++ t
  else if isUndoOrRedo c then t ++ " last change"
  else t

-- | select a named entity
data SelectCmd =
    File -- read library from file
  | Lib  -- allows to move to an imported library
  | Node
  | ComorphismTranslation
  | Prover
  | Goal  -- a single goal for an automatic prover
  | ConsistencyChecker
  | Link
  | ConservativityChecker
    deriving (Enum, Bounded)

selectCmdList :: [SelectCmd]
selectCmdList = [minBound .. maxBound]

describeSelectCmd :: SelectCmd -> String
describeSelectCmd cmd = case cmd of
  File -> "read file"
  Lib -> "select library"
  Node -> "select node"
  ComorphismTranslation -> "choose translation"
  Prover -> "choose prover"
  Goal -> "set goal"
  ConsistencyChecker -> "choose consistency checker"
  Link -> "select link"
  ConservativityChecker -> "choose conservativity checker"

data InspectCmd =
    CmdList -- all possible commands
  | Libs  -- all imported libraries
  | Nodes -- of library
  | Edges
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
  | EdgeInfo -- of a selected link
    deriving (Eq, Ord, Enum, Bounded)

inspectCmdList :: [InspectCmd]
inspectCmdList = [minBound .. maxBound]

showInspectCmd :: InspectCmd -> String
showInspectCmd cmd = case cmd of
  CmdList -> "Commands"-- all possible commands
  Libs -> "Library Names"
  Nodes -> "Nodes"
  Edges -> "Edges"
  UndoHist -> "Undo-History"
  RedoHist -> "Redo-History"
  NodeInfo -> "Node-Info"
  Theory -> "Computed Theory"
  AllGoals -> "All Goals"
  ProvenGoals -> "Proven Goals"
  UnprovenGoals -> "Unproven Goals"
  Axioms -> "All Axioms"
  LocalAxioms -> "Local Axioms"
  Taxonomy -> "Taxonomy"
  Concept -> "Concept"
  EdgeInfo -> "Edge-Info"

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

{- unsafe commands are needed to
delete or add
Links, Nodes, Symbols from Signatures, and sentences

A sequence of such unsafe operations should be check by hets, if they will
result in a consistent development graph, possibly indicating why not.  -}



