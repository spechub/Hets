{- |
Module      :  $Header$
Copyright   :  (c) Klaus Luettich, Heng Jiang, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Structured analysis of the import structure of OWL-DL files. circular
imports result in a united theory of all members of the circle.
-}

module OWL.StructureAnalysis (getNameFromNode, buildDevGraph) where


import Static.GTheory
import Static.DevGraph

import OWL.Sign
import OWL.Logic_OWL
import OWL.AS
import OWL.Namespace

import Logic.Comorphism
import Logic.Grothendieck
import Logic.Logic
import Logic.ExtSign
import Logic.Prover
import Logic.Coerce

import Common.Id
import Common.Result
import Common.ExtSign

import qualified Data.Map as Map
import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Query.DFS as DFS
import Data.Maybe (fromJust)
import Data.Char (isDigit)
import Data.List

buildDevGraph :: OntologyMap -> (OntologyMap, DGraph)
buildDevGraph ontoMap =
    if (detectLoop sscList) then
       rebuildDGraph sscList ontoMap' dg
      else (ontoMap', dg)

   where (ontoMap', dg) =
             Map.foldWithKey graphFromMap
                    (ontoMap, emptyDG)
                    ontoMap
         sscList = DFS.scc $ dgBody dg

-- | detect loop reference in graph
detectLoop :: [[Node]] -> Bool
detectLoop nl =
    any (\x -> length x > 1) nl

graphFromMap :: String -> OntologyFile
             -> (OntologyMap, DGraph)
             -> (OntologyMap, DGraph)
graphFromMap ouri (OntologyFile _ onto) (ontoMap, dg) =
    let existedLNodes = labNodesDG dg
        currentSign = mkExtSign $ simpleSign $ mkQName ouri
       -- get current node
        (lnode, ontoMap1) =
            createLNodes [ouri] existedLNodes ontoMap
        cl@(ind, _) = head lnode
        impList = map localPart $ importsList onto -- searchImports onto
       -- create LabNodes from imports list, this incl. the LNodes
       -- which been existed because of building of edge.
        (tagLNodes, ontoMap2) =
            createLNodes impList (nub (cl:existedLNodes)) ontoMap1
       -- if tagnode existed then it muss be reduced.
        newLNodes = reduceLNodes (cl:tagLNodes) dg

        morphism = idComorphism (Logic OWL)
        Result _ (Just comorphism) =
             gEmbedComorphism morphism (G_sign OWL currentSign startSigId)

        -- to add ids into edges
        ledgeList = map (\ (indT, _) ->
                                (ind, indT, globDefLink comorphism
                                    DGLinkImports))
                            tagLNodes
    in (ontoMap2, insEdgesDG ledgeList (insNodesDG newLNodes dg))

createLNodes :: [String] -> [LNode DGNodeLab]
             -> OntologyMap
             -> ([LNode DGNodeLab], OntologyMap)
createLNodes [] _ om = ([], om)
createLNodes (hs:rs) exLNodes om =
    let lnode@(_, currentLN) =
            buildLNodeFromStr hs ((length exLNodes)-1)
    in  -- if the node already existed muss be anyhow also created
        -- for building of edges. But the ontology map need not to
        -- change
        if isEqLNode currentLN exLNodes then
           let (newLNodes, ontoMap') = createLNodes rs exLNodes om
           in (
               (getLnode currentLN exLNodes):newLNodes,
               ontoMap'
              )
           else let lnode' = disambiguateName lnode exLNodes
                    (newLNodes, ontoMap') =
                        createLNodes rs (lnode':exLNodes) om
                    sid = getName $ dgn_name $ snd lnode'
                in
                   (
                     lnode':newLNodes,
                     Map.delete hs (Map.insert (show sid)
                                    (case Map.lookup hs ontoMap' of
                                      Just res -> res
                                      Nothing -> emptyOntologyFile
                                    )
                                    ontoMap')
                    )

    where
          -- get (LNode DGNodeLab) with LabNode
          getLnode _ [] = error "LNode not found"
          getLnode node (hx:rx) | dgn_theory node == (dgn_theory $ snd hx) = hx
                                | otherwise = getLnode node rx

          isEqLNode :: DGNodeLab -> [LNode DGNodeLab] -> Bool
          isEqLNode cn exn =
              any (\x -> (dgn_theory cn) == (dgn_theory $ snd x)) exn

          disambiguateName :: (LNode DGNodeLab)
                           -> [LNode DGNodeLab]
                           -> (LNode DGNodeLab)
          disambiguateName (ind, dgn) exn =
            let name@(NodeName sid u1 u2 _) = dgn_name dgn
                nameSet = map (dgn_name . snd) exn
                name' = if name `elem` nameSet then
                           let n = show sid
                               nsid = if isDigit $ head $ reverse n then
                                         take ((length n) - 1) n
                                         else n
                           in fromJust $ find (not . flip elem nameSet)
                              [NodeName (mkSimpleId $ nsid ++ show i) u1 u2 []
                               | i <- [1 :: Int ..]]
                         else name
            in  (ind, dgn {dgn_name = name'})

buildLNodeFromStr :: String -> Int -> (LNode DGNodeLab)
buildLNodeFromStr u i =
    let name = uriToName u
        nodeName = makeName $ mkSimpleId name
        currentSign = mkExtSign $ simpleSign $ mkQName u
    in  (i+1, newNodeLab nodeName DGBasic
              $ noSensGTheory OWL currentSign startSigId)

-- remove existing nodes in graph
reduceLNodes :: [LNode DGNodeLab] -> DGraph -> [LNode DGNodeLab]
reduceLNodes l dg = filter ( \ (ind, _) -> not $ gelemDG ind dg) l

rebuildDGraph :: [[Node]] -> OntologyMap -> DGraph -> (OntologyMap, DGraph)
rebuildDGraph [] ontoMap dg = (ontoMap, dg)
rebuildDGraph (hd:rs) ontoMap dg
   | length hd <= 1 = rebuildDGraph rs ontoMap dg
   | otherwise      =
       let (ontoMap', dg') = integrateScc hd ontoMap dg
       in   rebuildDGraph rs ontoMap' dg'

integrateScc :: [Node] -> OntologyMap -> DGraph -> (OntologyMap, DGraph)
integrateScc nodeList ontoMap dg =
    let decomps = map (fromJust . fst . flip matchDG dg) nodeList
        (_, _, lnodes,_) = unzip4 decomps
        dgnNames = map (getNameFromNode . dgn_name) lnodes
        theories = map dgn_theory lnodes
        ontologies = map (\x -> case Map.lookup x ontoMap of
                                Just res -> res
                                Nothing -> emptyOntologyFile
                         ) dgnNames
        newName = makeName $ mkSimpleId $ (\z -> take ((length z) -1) z) $
                    foldr (\x y -> x ++ "_" ++ y) "" dgnNames
        newTheory = integrateTheory theories
        newNodeNum = noNodesDG dg
    in ( Map.insert (getNameFromNode newName)
                    (foldl integrateOntologyFile emptyOntologyFile
                           ontologies)
                    (Map.filterWithKey (\x _ -> not $ x `elem` dgnNames)
                     ontoMap)
       , delNodesDG nodeList $ changeEdges decomps newNodeNum $ insNodeDG
             (newNodeNum, newNodeLab newName DGintegratedSCC newTheory) dg)

-- simple integrate Theory
integrateTheory :: [G_theory] -> G_theory
integrateTheory theories =
  foldl assembleTheories emptyOWLTheory theories
   where
    assembleTheories :: G_theory -> G_theory -> G_theory
    assembleTheories (G_theory lid1 sign1 _ theSen1 _)
                     (G_theory lid2 sign2 _ theSen2 _) =
              let thSen2' = maybe (error "could not coerce sentences")
                        id (coerceThSens lid2 lid1 "" theSen2)
                  sign2' = maybe (error "could not coerce sign")
                        id (coerceSign lid2 lid1 "" sign2)
                  csign = case ext_signature_union lid1 sign2' sign1 of
                          Result dgs mv ->
                              maybe (error ("sig_union"++show dgs)) id mv
              in G_theory lid1 csign startSigId
                     (joinSens theSen1 thSen2') startThId

getNameFromNode :: NodeName -> String
getNameFromNode = show . getName

changeEdges :: [Context DGNodeLab DGLinkLab] -> Node -> DGraph -> DGraph
changeEdges [] _ dg = dg
changeEdges ((fromNodes, n, _, toNodes):r) newNode dg =
    changeEdges r newNode $ changeTo toNodes $ changeFrom fromNodes dg
    where changeFrom :: [(DGLinkLab, Node)] -> DGraph -> DGraph
          changeFrom [] dg2 = dg2
          changeFrom ((dgLink,fn):rf) dg2
            | fn `gelemDG` dg2 =
                changeFrom rf $ insEdgeDG (fn, newNode, dgLink) $
                                    delEdgeDG (fn, n) dg2
            | otherwise = changeFrom rf dg2

          changeTo :: [(DGLinkLab, Node)] -> DGraph -> DGraph
          changeTo [] dg2 = dg2
          changeTo ((dgLink,tn):rf) dg2
            | tn `gelemDG` dg2 =
                changeTo rf $ insEdgeDG (newNode, tn, dgLink) $
                                    delEdgeDG (n, tn) dg2
            | otherwise = changeTo rf dg2

emptyOWLTheory:: G_theory
emptyOWLTheory = noSensGTheory OWL (mkExtSign emptySign) startSigId
