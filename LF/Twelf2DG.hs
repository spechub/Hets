{- |
Module      :  $Header$
Description :  Conversion of Twelf files to Development Graphs
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}
module LF.Twelf2DG where

import Static.DevGraph
import Static.ComputeTheory
import Static.GTheory

import Logic.Grothendieck
import Logic.ExtSign
import Logic.Logic

import LF.Twelf2GR
import LF.Sign
import LF.Morphism
import LF.Logic_LF

import Data.Graph.Inductive.Graph (Node)
import qualified Data.Map as Map

import Common.LibName
import Common.Id
import Common.Keywords
import qualified Common.Consistency as Cons

import Driver.Options

type NODE_MAP = Map.Map NODE Node

-- analyzes the given Twelf file
anaTwelfFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaTwelfFile _ fp = do
  file <- resolveToCur fp
  let name = emptyLibName file
  (libs,bs) <- twelf2GR file (Map.empty,[])
  let libenv = makeLibEnv libs bs
  return $ Just (name,libenv)

{- generates a library environment from libraries of signatures and morphisms
   the list of library names stores the order in which they were added -}
makeLibEnv :: LIBS -> [BASE] -> LibEnv
makeLibEnv libs bs = fst $
  foldl ( \ (le,nm) b ->
            let (sigs,morphs) = Map.findWithDefault
                    (error "Library cannot be found.") b libs
                ln = emptyLibName b
                le1 = Map.insert ln emptyDG le
                (le2,nm1) = addNodes le1 nm b sigs
                le3 = addLinks le2 nm1 b morphs
                dg = computeDGraphTheories le3 $ lookupDGraph ln le3
                le4 = Map.insert ln dg le3
                in (le4,nm1)
        ) (emptyLibEnv,Map.empty) bs

{- adds nodes to the library environment
   node map returned for reference when adding links -}
addNodes :: LibEnv -> NODE_MAP -> BASE -> SIGS -> (LibEnv,NODE_MAP)
addNodes le nm b sigs =
  let ln = emptyLibName b
      (dg2,nm1) = Map.foldWithKey
         (\ m sig (dg,nmap) ->
            let (n,dg1) = addSigToDG sig dg
                nmap1 = Map.insert (b,m) n nmap
                in (dg1,nmap1)
         ) (lookupDGraph ln le, nm) sigs
      le1 = Map.insert ln dg2 le
      in (le1,nm1)

-- inserts a signature as a node to the development graph
addSigToDG :: Sign -> DGraph -> (Node,DGraph)
addSigToDG sig dg =
  let node = getNewNodeDG dg
      name = Token (sigModule sig) nullRange
      nodeName = emptyNodeName { getName = name }
      info = newNodeInfo DGBasic
      extSign = makeExtSign LF sig
      gth = noSensGTheory LF extSign startSigId
      nodeLabel = newInfoNodeLab nodeName info gth
      dg1 = insNodeDG (node,nodeLabel) dg
      emptyNode = EmptyNode $ Logic LF
      genSig = GenSig emptyNode [] emptyNode
      nodeSig = NodeSig node $ G_sign LF extSign startSigId
      gEntry = SpecEntry $ ExtGenSig genSig nodeSig
      dg2 = dg1 { globalEnv = Map.insert name gEntry $ globalEnv dg1 }
      in (node,dg2)

-- adds links to the library environment
addLinks :: LibEnv -> NODE_MAP -> BASE -> MORPHS -> LibEnv
addLinks le nm b morphs =
  let ln = emptyLibName b
      dg1 = Map.fold (\ morph dg -> addMorphToDG morph dg nm le)
              (lookupDGraph ln le) morphs
      in Map.insert ln dg1 le

-- inserts a morphism as a link to the development graph
addMorphToDG :: Morphism -> DGraph -> NODE_MAP -> LibEnv -> DGraph
addMorphToDG morph dg nm le =
  let b = morphBase morph
      m = morphModule morph
      n = morphName morph
      k = morphType morph
      gMorph = gEmbed $ G_morphism LF morph startMorId
      thmStatus = Proven (DGRule "Type-checked") emptyProofBasis
      linkKind = case k of
          Definitional -> DefLink
          Postulated -> ThmLink thmStatus
          Unknown -> error "Unknown morphism type."
      consStatus = ConsStatus Cons.None Cons.None LeftOpen
      linkType = ScopedLink Global linkKind consStatus
      linkLabel = defDGLink gMorph linkType SeeTarget
      (node1,dg1) = addRefNode (source morph) (b,dg) nm le
      (node2,dg2) = addRefNode (target morph) (b,dg1) nm le
      (_,dg3) = insLEdgeDG (node1,node2,linkLabel) dg2

      in if (k == Definitional && null n) then dg3 else
        let n' = if (k == Postulated) then m else m ++ sigDelimS ++ n
            name = Token n' nullRange
            extSignSrc = makeExtSign LF $ source morph
            extSignTar = makeExtSign LF $ target morph
            nodeSigSrc = NodeSig node1 $ G_sign LF extSignSrc startSigId
            nodeSigTar = NodeSig node2 $ G_sign LF extSignTar startSigId
            emptyNode = EmptyNode $ Logic LF
            genSigTar = GenSig emptyNode [] emptyNode
            extGenSigTar = ExtGenSig genSigTar nodeSigTar
            gEntry = StructEntry $ ExtViewSig nodeSigSrc gMorph extGenSigTar
            dg4 = dg3 { globalEnv = Map.insert name gEntry $ globalEnv dg3 }
            in dg4

-- constructs a reference node to the specified signature, if needed
addRefNode :: Sign -> (BASE,DGraph) -> NODE_MAP -> LibEnv -> (Node,DGraph)
addRefNode sig (base,dg) nm le =
  let b = sigBase sig
      m = sigModule sig
      nod = Map.findWithDefault (error "Node number cannot be found.") (b,m) nm
      in if (b == base) then (nod,dg) else
            let info = newRefInfo (emptyLibName b) nod
                refNodeM = lookupInAllRefNodesDG info dg
                in case refNodeM of
                        Just refNode -> (refNode,dg)
                        Nothing -> insRefSigToDG sig info dg le

-- inserts a signature as a reference node to the development graph
insRefSigToDG :: Sign -> DGNodeInfo -> DGraph -> LibEnv -> (Node,DGraph)
insRefSigToDG sig info dg le =
  let node = getNewNodeDG dg
      m = sigModule sig
      nodeName = emptyNodeName { getName = Token m nullRange }
      extSign = makeExtSign LF sig
      gth = noSensGTheory LF extSign startSigId
      nodeLabel1 = newInfoNodeLab nodeName info gth
      refDG = lookupDGraph (ref_libname info) le
      refGlobTh = globalTheory $ labDG refDG $ ref_node info
      nodeLabel2 = nodeLabel1 { globalTheory = refGlobTh}
      dg1 = insNodeDG (node,nodeLabel2) dg
      dg2 = addToRefNodesDG node info dg1
      in (node,dg2)
