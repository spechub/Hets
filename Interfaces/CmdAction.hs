{- |
Module      :  $Header$
Description :  command action associations for all interfaces
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

association of some commands to actions on development graphs
-}

module Interfaces.CmdAction where

import Proofs.QualifyNames (qualifyLibEnv)
import Proofs.DGFlattening
import Proofs.Freeness (freeness)
import Proofs.NormalForm (normalForm)
import Proofs.Automatic (automatic)
import Proofs.Global (globSubsume, globDecomp)
import Proofs.Local (localInference, locDecomp)
import Proofs.Composition (composition, compositionCreatingEdges)
import Proofs.HideTheoremShift (automaticHideTheoremShift)
import Proofs.TheoremHideShift (theoremHideShift)
import Proofs.Conservativity (conservativity)
import Proofs.ComputeColimit (computeColimit)
import Proofs.TriangleCons (triangleCons)

import Static.DevGraph

import Interfaces.Command

import Common.LibName
import Common.Result

globLibAct :: [(GlobCmd, LibName -> LibEnv -> LibEnv)]
globLibAct =
  [ (Automatic, automatic)
  , (GlobDecomp, globDecomp)
  , (GlobSubsume, globSubsume)
  , (LocalDecomp, locDecomp)
  , (LocalInference, localInference)
  , (CompositionProveEdges, composition)
  , (CompositionCreateEdges, compositionCreatingEdges)
  , (Conservativity, conservativity)
  , (HideThmShift, automaticHideTheoremShift) ]

globLibResultAct :: [(GlobCmd, LibName -> LibEnv -> Result LibEnv)]
globLibResultAct =
  [ (ThmHideShift, theoremHideShift)
  , (Colimit, computeColimit)
  , (NormalForm, normalForm)
  , (TriangleCons, triangleCons)
  , (Freeness, freeness)
-- , (ThmFreeShift, theoremFreeShift)
  ]

allGlobLibAct :: [(GlobCmd, LibName -> LibEnv -> Result LibEnv)]
allGlobLibAct =
  map (\ (a, b) -> (a, \ n -> return . b n)) globLibAct
  ++ globLibResultAct
  ++ map (\ (a, b) -> (a, const b)) globResultAct

globResultAct :: [(GlobCmd, LibEnv -> Result LibEnv)]
globResultAct =
  [ (Importing, libFlatImports)
  , (DisjointUnion, libFlatDUnions)
  , (Renaming, libFlatRenamings)
  , (Hiding, libFlatHiding)
  , (Heterogeneity, libFlatHeterogen)
  , (QualifyNames, qualifyLibEnv) ]
