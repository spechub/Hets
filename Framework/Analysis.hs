{- |
Module      :  $Header$
Description :  Analyzes a logic definition 
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.Analysis ( anaLogicDef ) where

import Framework.AS

import qualified Data.Map as Map

import Static.DevGraph
import Static.GTheory

import Logic.Grothendieck
import Logic.ExtSign
import Logic.Logic

import Framework.Logic_Framework

-- analyzes a logic definition
anaLogicDef :: LogicDef -> LibEnv -> DGraph -> DGraph
anaLogicDef ld _ dg = addLogicDef2DG ld dg 

addLogicDef2DG :: LogicDef -> DGraph -> DGraph
addLogicDef2DG ld dg =
  let node = getNewNodeDG dg
      name = newlogicName ld
      nodeName = emptyNodeName { getName = name }
      info = newNodeInfo DGBasic
      extSign = makeExtSign Framework ld
      gth = noSensGTheory Framework extSign startSigId
      nodeLabel = newInfoNodeLab nodeName info gth
      dg1 = insNodeDG (node,nodeLabel) dg

      emptyNode = EmptyNode $ Logic Framework
      genSig = GenSig emptyNode [] emptyNode
      nodeSig = NodeSig node $ G_sign Framework extSign startSigId
      gEntry = SpecEntry $ ExtGenSig genSig nodeSig
      dg2 = dg1 { globalEnv = Map.insert name gEntry $ globalEnv dg1 }
      in dg2
