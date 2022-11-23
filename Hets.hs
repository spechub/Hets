module Hets (
    -- Hets.Commands
    automatic
   , globalSubsume
   , globalDecomposition
   , localInference
   , localDecomposition
   , compositionProveEdges
   , conservativity
   , automaticHideTheoremShift
   , theoremHideShift
   , computeColimit
   , normalForm
   , triangleCons
   , freeness
   , libFlatImports
   , libFlatDUnions
   , libFlatRenamings
   , libFlatHiding
   , libFlatHeterogen
   , qualifyLibEnv
   , loadLibrary
   , getGraphForLibrary
   , getNodesFromDevelopmentGraph
   , getLNodesFromDevelopmentGraph
   , usableProvers
   , autoProveNode
   , proveNode 
) where

import Hets.Commands