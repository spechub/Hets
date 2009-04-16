{- |
Module      :  $Header$
Description :  command action associations for all interfaces
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

association of some commands to actions on development graphs
-}

module Interfaces.CmdAction where

import Proofs.QualifyNames (qualifyLibEnv)
import Proofs.DGFlattening
import Proofs.NormalForm (normalForm)
import Proofs.Automatic(automatic)
import Proofs.Global (globSubsume, globDecomp)
import Proofs.Local (localInference, locDecomp)
import Proofs.Composition (composition, compositionCreatingEdges)
import Proofs.HideTheoremShift (automaticHideTheoremShift)
import Proofs.TheoremHideShift (theoremHideShift)
import Proofs.ComputeColimit (computeColimit)

import Static.DevGraph

import Interfaces.Command

import Common.LibName
import Common.Result

globLibAct :: [(GlobCmd, LIB_NAME -> LibEnv -> LibEnv)]
globLibAct =
  [ (Automatic, automatic)
  , (GlobDecomp, globDecomp)
  , (GlobSubsume, globSubsume)
  , (LocalDecomp, locDecomp)
  , (LocalInference, localInference)
  , (CompositionProveEdges, composition)
  , (CompositionCreateEdges, compositionCreatingEdges)
  , (HideThmShift, automaticHideTheoremShift) ]

globLibResultAct :: [(GlobCmd, LIB_NAME -> LibEnv -> Result LibEnv)]
globLibResultAct =
  [ (ThmHideShift, theoremHideShift)
  , (Colimit, computeColimit)
  , (NormalForm, normalForm) ]

globResultAct :: [(GlobCmd, LibEnv -> Result LibEnv)]
globResultAct =
  [ (Importing, libEnv_flattening_imports)
  , (DisjointUnion, libEnv_flattening_dunions)
  , (Renaming, libEnv_flattening_renamings)
  , (Hiding, libEnv_flattening_hiding)
  , (Heterogeneity, libEnv_flattening_heterogen)
  , (QualifyNames, qualifyLibEnv) ]
