{- |
Description :  Exports HETS functionality as a structured API
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}

module HetsAPI (
    -- HetsAPI.Commands
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
   , getUsableProvers
   , proveNode 
) where

import HetsAPI.Commands