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

import Common.Utils

import Data.Char
import Data.List

data GlobCmd =
    Automatic
  | GlobDecomp
  | GlobSubsume
  | LocalDecomp
  | LocalInference
  | CompositionProveEdges
  | CompositionCreateEdges
  | ThmHideShift
  | HideThmShift
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
  | ProveCurrent
  | DropTranslation
    deriving (Eq, Ord, Enum, Bounded)

globCmdList :: [GlobCmd]
globCmdList = [minBound .. maxBound]

menuTextGlobCmd :: GlobCmd -> String
menuTextGlobCmd cmd = case cmd of
  Automatic -> "Automatic"
  GlobDecomp -> "Global-Decomposition"
  GlobSubsume -> "Global-Subsumption"
  LocalDecomp -> "Local-Decomposition"
  LocalInference -> "Local-Inference"
  CompositionProveEdges -> "Prove composed edges"
  CompositionCreateEdges -> "Create composed proven edges"
  ThmHideShift -> "Theorem-Hide-Shift"
  HideThmShift -> "Hide-Theorem-Shift"
  Colimit -> "Compute colimit"
  NormalForm -> "Compute normal form"
  QualifyNames -> "Qualify all names"
  UndoCmd -> "Undo"
  RedoCmd -> "Redo"
  Importing -> "Importing"
  DisjointUnion -> "Disjoint union"
  Renaming -> "Renaming"
  Hiding -> "Hiding"
  Heterogeneity -> "Heterogeneity"
  ProveCurrent -> "Prove"
  DropTranslation -> "Drop-Translations"

-- | even some short names for the command line interface
cmdlGlobCmd :: GlobCmd -> String
cmdlGlobCmd cmd = case cmd of
  Automatic -> "auto"
  GlobDecomp -> "glob-decomp"
  GlobSubsume -> "global-subsume"
  LocalDecomp -> "loc-decomp"
  LocalInference -> "local-infer"
  CompositionProveEdges -> "comp"
  CompositionCreateEdges -> "comp-new"
  ThmHideShift -> "thm-hide"
  HideThmShift -> "hide-thm"
  _ -> map toLower $ menuTextGlobCmd cmd

isDgRule :: GlobCmd -> Bool
isDgRule c = c <= HideThmShift

isFlatteningCmd :: GlobCmd -> Bool
isFlatteningCmd c = c >= Importing && c <= Heterogeneity

isUndoOrRedo :: GlobCmd -> Bool
isUndoOrRedo c = elem c [UndoCmd, RedoCmd]

describeGlobCmd :: GlobCmd -> String
describeGlobCmd c =
  let mt = menuTextGlobCmd c
      t = map toLower mt in
  case c of
  Automatic -> "Apply automatic tactic"
  CompositionProveEdges -> t
  CompositionCreateEdges -> t
  QualifyNames -> "Qualify and disambiguate all signature names"
  NormalForm -> "Compute normal forms for nodes with incoming hiding links"
  Importing -> "Flatten all theories and delete all importing links"
  DisjointUnion -> "Create intersection nodes and ensure only disjoint unions"
  Hiding -> "Delete all hiding links"
  ProveCurrent -> "Applies selected prover to selected goals"
  DropTranslation -> "Drops any selected comorphism"
  _ -> if isDgRule c then "Apply rule " ++ t else
    if isFlatteningCmd c then "Flatten out " ++ t else
    if isUndoOrRedo c then mt ++ " last change" else t

globCmdNameStr :: GlobCmd -> String
globCmdNameStr c = let s = cmdlGlobCmd c in
  if isDgRule c then "dg-all " ++ s else
  if isFlatteningCmd c then "flattening " ++ s else s

-- | select a named entity
data SelectCmd =
    LibFile -- read library from file
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

selectCmdNameStr :: SelectCmd -> String
selectCmdNameStr cmd = case cmd of
  LibFile -> "use"
  Lib -> "library"
  Node -> "dg basic"
  ComorphismTranslation -> "translate"
  Prover -> "prover"
  Goal -> "set goals"
  ConsistencyChecker -> "cons-checker"
  Link -> "link"
  ConservativityChecker -> "conservativity-check"

describeSelectCmd :: SelectCmd -> String
describeSelectCmd cmd = case cmd of
  LibFile -> "Read HetCASL file"
  Lib -> "Select library"
  Node -> "Select node"
  ComorphismTranslation -> "Choose translation"
  Prover -> "Choose prover"
  Goal -> "Set goal"
  ConsistencyChecker -> "Choose consistency checker"
  Link -> "Select link"
  ConservativityChecker -> "Choose conservativity checker"

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
  CmdList -> "Details" -- all possible commands
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

requiresNode :: InspectCmd -> Bool
requiresNode ic = ic >= NodeInfo && ic < EdgeInfo

data Command =
    GlobCmd GlobCmd
  | SelectCmd SelectCmd String
  | TimeLimit Int -- set a time limit for an automatic  prover
  | SetAxioms [String] -- set the axiom list for an automatic  prover
  | IncludeProvenTheorems Bool -- should proven theorems be added as axioms
  | InspectCmd InspectCmd
  | CommentCmd String
  | GroupCmd [Command] -- just to group commands in addCommandHistoryToState

mkSelectCmd :: SelectCmd -> Command
mkSelectCmd s = SelectCmd s ""

cmdInputStr :: Command -> String
cmdInputStr cmd = case cmd of
  SelectCmd _ t -> t
  TimeLimit l -> show l
  SetAxioms as -> unwords as
  _ -> ""

setInputStr :: String -> Command -> Command
setInputStr str cmd = case cmd of
  SelectCmd s _ -> SelectCmd s str
  TimeLimit l -> TimeLimit $ case readMaybe str of
    Just n -> n
    _ -> l
  SetAxioms _ -> SetAxioms $ words str
  _ -> cmd

cmdNameStr :: Command -> String
cmdNameStr cmd = case cmd of
  GlobCmd g -> globCmdNameStr g
  SelectCmd s _ -> selectCmdNameStr s
  TimeLimit _ -> "set time-limit"
  SetAxioms _ -> "set axioms"
  IncludeProvenTheorems b -> "set include-theorems " ++ map toLower (show b)
  InspectCmd i -> (if i > Edges then "show-" else "")
    ++ map (\ c -> if c == ' ' then '-' else toLower c) (showInspectCmd i)
  CommentCmd _ -> "#"
  GroupCmd _ -> ""

-- | show command with arguments
showCmd :: Command -> String
showCmd c = case c of
  SelectCmd _ t -> cmdNameStr c  ++ " " ++ t
  TimeLimit l -> cmdNameStr c ++ " " ++ show l
  SetAxioms as -> unwords $ cmdNameStr c : as
  CommentCmd s -> cmdNameStr c ++ s
  GroupCmd l -> intercalate "\n" $ map showCmd l
  _ -> cmdNameStr c

describeCmd :: Command -> String
describeCmd cmd = case cmd of
  GlobCmd g -> describeGlobCmd g
  SelectCmd s _ -> describeSelectCmd s
  TimeLimit _ -> "Set the time-limit for the next proof"
  SetAxioms _ -> "Set the axioms used for the next proof"
  IncludeProvenTheorems b -> (if b then "I" else "Do not i")
    ++ "nclude proven theorems"
  InspectCmd i -> "Show " ++ showInspectCmd i
  CommentCmd _ -> "Line comment"
  GroupCmd _ -> "Grouping several commands"

commandList :: [Command]
commandList =
  map GlobCmd globCmdList
  ++ map (\ s -> SelectCmd s "") selectCmdList
  ++ [TimeLimit 0, SetAxioms []]
  ++ map IncludeProvenTheorems [False, True]
  ++ map InspectCmd inspectCmdList

{- unsafe commands are needed to
delete or add
Links, Nodes, Symbols from Signatures, and sentences

A sequence of such unsafe operations should be checked by hets, if they will
result in a consistent development graph, possibly indicating why not.  -}
