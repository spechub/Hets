{- |
Module      :  ./Interfaces/Command.hs
Description :  development graph commands for all interfaces
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

data types for development graph commands to be invoked via the GUI, the
command-line-interface (CMDL), and other tools
-}

module Interfaces.Command where

import Common.Utils

import Data.Maybe
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
  | Conservativity
  | ThmHideShift
  | HideThmShift
  | Colimit
  | NormalForm
  | TriangleCons
  | Freeness
  | ThmFreeShift
  | QualifyNames
  | UndoCmd
  | RedoCmd
    -- Flattening command
  | Importing
  | DisjointUnion
  | Renaming
  | Hiding
  | Heterogeneity
  | ProveCurrent  -- CMDL prover activation
  | DisproveCurrent
  | CheckConsistencyCurrent
  | CheckConservativityAll
  | DropTranslation -- stop composing comorphisms to previous ones
    deriving (Eq, Ord, Enum, Bounded, Show)

globCmdList :: [GlobCmd]
globCmdList = [minBound .. maxBound]

-- list of command names in the gui interface
menuTextGlobCmd :: GlobCmd -> String
menuTextGlobCmd cmd = case cmd of
  Automatic -> "Auto-DG-Prover"
  GlobDecomp -> "Global-Decomposition"
  GlobSubsume -> "Global-Subsumption"
  LocalDecomp -> "Local-Decomposition"
  LocalInference -> "Local-Inference"
  CompositionProveEdges -> "Prove composed edges"
  CompositionCreateEdges -> "Create composed proven edges"
  Conservativity -> "Conservativity"
  ThmHideShift -> "Theorem-Hide-Shift"
  ThmFreeShift -> "Theorem-Free-Shift"
  HideThmShift -> "Hide-Theorem-Shift"
  Colimit -> "Compute colimit"
  NormalForm -> "Compute normal form"
  TriangleCons -> "Triangle-Cons"
  QualifyNames -> "Qualify all names"
  UndoCmd -> "Undo"
  RedoCmd -> "Redo"
  Importing -> "Importing"
  DisjointUnion -> "Disjoint union"
  Renaming -> "Renaming"
  Hiding -> "Hiding"
  Freeness -> "Freeness"
  Heterogeneity -> "Heterogeneity"
  ProveCurrent -> "Prove"
  DisproveCurrent -> "Disprove"
  CheckConsistencyCurrent -> "Check consistency"
  CheckConservativityAll -> "Globally check conservativity"
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
  Conservativity -> "cons"
  ThmHideShift -> "thm-hide"
  HideThmShift -> "hide-thm"
  _ -> map (\ c -> if c == ' ' then '-' else toLower c) $ menuTextGlobCmd cmd

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
  _ | isDgRule c -> "Apply rule " ++ t
    | isFlatteningCmd c -> "Flatten out " ++ t
    | isUndoOrRedo c -> mt ++ " last change"
  _ -> t

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
  | ConservativityCheckerOpen
  | ConservativityChecker
    deriving (Eq, Ord, Enum, Bounded, Show)

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
  ConservativityCheckerOpen -> "conservativity-check-open"
  ConservativityChecker -> "conservativity-check"

describeSelectCmd :: SelectCmd -> String
describeSelectCmd cmd = case cmd of
  LibFile -> "Read DOL file"
  Lib -> "Select library"
  Node -> "Select node"
  ComorphismTranslation -> "Choose translation"
  Prover -> "Choose prover"
  Goal -> "Set one or more space separated goal names"
  ConsistencyChecker -> "Choose consistency checker"
  Link -> "Select link"
  ConservativityChecker -> "Choose edges for a conservativity checker"
  ConservativityCheckerOpen -> "Choose open edges for a conservativity checker"

data InspectCmd =
    Libs  -- all imported libraries
  | Nodes -- of library
  | Edges
  | UndoHist
  | RedoHist
  | EdgeInfo -- of a selected link
  | CurrentComorphism
  | LocalAxioms
  | NodeInfo
  | ComorphismsTo
  | TranslatedTheory
  | Theory
  | AllGoals
  | ProvenGoals
  | UnprovenGoals
  | Axioms
  | Taxonomy
  | Concept
    deriving (Eq, Ord, Enum, Bounded, Show)

inspectCmdList :: [InspectCmd]
inspectCmdList = [minBound .. maxBound]

showInspectCmd :: InspectCmd -> String
showInspectCmd cmd = case cmd of
  Libs -> "Library Names"
  Nodes -> "Nodes"
  Edges -> "Edges"
  ComorphismsTo -> "Comorphisms to"
  CurrentComorphism -> "Current Comorphism"
  TranslatedTheory -> "Translated Theory"
  UndoHist -> "Undo-History"
  RedoHist -> "Redo-History"
  EdgeInfo -> "Edge-Info"
  LocalAxioms -> "Local Axioms"
  NodeInfo -> "Node-Info"
  Theory -> "Computed Theory"
  AllGoals -> "All Goals"
  ProvenGoals -> "Proven Goals"
  UnprovenGoals -> "Unproven Goals"
  Axioms -> "All Axioms"
  Taxonomy -> "Taxonomy"
  Concept -> "Concept"

requiresNode :: InspectCmd -> Bool
requiresNode ic = ic >= LocalAxioms

data ChangeCmd =
    Expand
  | AddView
    deriving (Eq, Ord, Enum, Bounded, Show)

describeChangeCmd :: ChangeCmd -> String
describeChangeCmd cmd = case cmd of
   Expand -> "Extend current node"
   AddView -> "Add a view"

changeCmdList :: [ChangeCmd]
changeCmdList = [minBound .. maxBound]

changeCmdNameStr :: ChangeCmd -> String
changeCmdNameStr cmd = case cmd of
  Expand -> "expand"
  AddView -> "addview"


data Command =
    GlobCmd GlobCmd
  | SelectCmd SelectCmd String
  | TimeLimit Int -- set a time limit for an automatic  prover
  | SetAxioms [String] -- set the axiom list for an automatic  prover
  | ShowOutput Bool -- show model
  | IncludeProvenTheorems Bool -- should proven theorems be added as axioms
  | InspectCmd InspectCmd (Maybe String)
  | CommentCmd String
  | GroupCmd [Command] -- just to group commands in addCommandHistoryToState
  | ChangeCmd ChangeCmd String
  | HelpCmd
  | ExitCmd
  deriving (Show)

-- the same command modulo input argument
eqCmd :: Command -> Command -> Bool
eqCmd c1 c2 = case (c1, c2) of
  (GlobCmd g1, GlobCmd g2) -> g1 == g2
  (SelectCmd s1 _, SelectCmd s2 _) -> s1 == s2
  (TimeLimit _, TimeLimit _) -> True
  (SetAxioms _, SetAxioms _) -> True
  (IncludeProvenTheorems b1, IncludeProvenTheorems b2) -> b1 == b2
  (InspectCmd i1 m1, InspectCmd i2 m2) -> i1 == i2 && isJust m1 == isJust m2
  (CommentCmd _, CommentCmd _) -> True
  (HelpCmd, HelpCmd) -> True
  (ExitCmd, ExitCmd) -> True
  (GroupCmd l1, GroupCmd l2) -> and (zipWith eqCmd l1 l2)
    && length l1 == length l2
  _ -> False

mkSelectCmd :: SelectCmd -> Command
mkSelectCmd s = SelectCmd s ""

mkChangeCmd :: ChangeCmd -> Command
mkChangeCmd c = ChangeCmd c ""

cmdInputStr :: Command -> String
cmdInputStr cmd = case cmd of
  SelectCmd _ t -> t
  TimeLimit l -> show l
  SetAxioms as -> unwords as
  InspectCmd _ t -> fromMaybe "" t
  ChangeCmd _ t -> t
  _ -> ""

setInputStr :: String -> Command -> Command
setInputStr str cmd = case cmd of
  SelectCmd s _ -> SelectCmd s str
  TimeLimit l -> TimeLimit $ case readMaybe str of
    Just n -> n
    _ -> l
  SetAxioms _ -> SetAxioms $ words str
  InspectCmd i _ -> InspectCmd i $ Just str
  ChangeCmd c _ -> ChangeCmd c str
  _ -> cmd

cmdNameStr :: Command -> String
cmdNameStr cmd = case cmd of
  GlobCmd g -> globCmdNameStr g
  SelectCmd s _ -> selectCmdNameStr s
  TimeLimit _ -> "set time-limit"
  SetAxioms _ -> "set axioms"
  ShowOutput b -> "show-output " ++ map toLower (show b)
  IncludeProvenTheorems b -> "set include-theorems " ++ map toLower (show b)
  InspectCmd i s ->
    (if i > Edges then "show-" else "")
    ++ map (\ c -> if c == ' ' then '-' else toLower c) (showInspectCmd i)
    ++ (if i > LocalAxioms && isNothing s && i /= ComorphismsTo
        then "-current" else "")
  CommentCmd _ -> "#"
  HelpCmd -> "help"
  ExitCmd -> "quit"
  GroupCmd _ -> ""
  ChangeCmd c _ -> changeCmdNameStr c

-- | show command with arguments
showCmd :: Command -> String
showCmd c = let cn = cmdNameStr c in case c of
  SelectCmd _ t -> cn ++ " " ++ t
  TimeLimit l -> cn ++ " " ++ show l
  SetAxioms as -> unwords $ cn : as
  CommentCmd s -> cn ++ s
  GroupCmd l -> intercalate "\n" $ map showCmd l
  InspectCmd _ t -> cn ++ " " ++ fromMaybe "" t
  ChangeCmd _ t -> cmdNameStr c ++ " " ++ t
  ShowOutput b -> cn ++ show b
  _ -> cn

describeCmd :: Command -> String
describeCmd cmd = case cmd of
  GlobCmd g -> describeGlobCmd g
  SelectCmd s _ -> describeSelectCmd s
  TimeLimit _ -> "Set the time-limit for the next proof"
  SetAxioms _ -> "Set the axioms used for the next proof"
  ShowOutput b -> (if b then "S" else "Do not s")
    ++ "how model"
  IncludeProvenTheorems b -> (if b then "I" else "Do not i")
    ++ "nclude proven theorems"
  InspectCmd i t -> if i == ComorphismsTo
   then "Show comorphisms from currently selected node(s) to target logic"
   else "Show " ++ showInspectCmd i
    ++ (if i > LocalAxioms && isNothing t then " of selected node" else "")
  CommentCmd _ -> "Line comment"
  HelpCmd -> "Show all available commands"
  ExitCmd -> "Quit"
  GroupCmd _ -> "Grouping several commands"
  ChangeCmd c _ -> describeChangeCmd c

commandList :: [Command]
commandList =
  map GlobCmd globCmdList
  ++ map mkSelectCmd selectCmdList
  ++ [TimeLimit 0, SetAxioms []]
  ++ map IncludeProvenTheorems [False, True]
  ++ map (flip InspectCmd $ Just "") inspectCmdList
  ++ map (flip ChangeCmd "") changeCmdList

{- unsafe commands are needed to
delete or add
Links, Nodes, Symbols from Signatures, and sentences

A sequence of such unsafe operations should be checked by hets, if they will
result in a consistent development graph, possibly indicating why not. -}
