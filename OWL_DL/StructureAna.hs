{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Heng Jiang, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Structured analysis of the import structure of OWL-DL files. circular
imports result in a united theory of all members of the circle.
-}

module OWL_DL.StructureAna where

import Static.GTheory
import Static.DevGraph
import Data.Graph.Inductive.Graph
import OWL_DL.Sign
import OWL_DL.Logic_OWL_DL
import OWL_DL.AS

import Logic.Grothendieck
import Logic.Logic
import Logic.Coerce
import Common.Id
import Common.Result
import Data.List
import Logic.Prover
import qualified Data.Map as Map
import Data.Maybe(fromJust)
import Data.Char(isDigit)
import OWL_DL.Namespace

type OntologyMap = Map.Map String Ontology

buildDevGraph :: OntologyMap -> (OntologyMap, DGraph)
buildDevGraph ontoMap =
    if detectLoop sscList then
       rebuildDGraph sscList ontoMap' dg
      else (ontoMap', dg)

   where (ontoMap', dg) =
             Map.foldWithKey graphFromMap
                    (ontoMap, emptyDG)
                    ontoMap
         sscList = sccDG dg

-- | detect loop reference in graph
detectLoop :: [[Node]] -> Bool
detectLoop nl =
    any (\x -> length x > 1) nl

graphFromMap :: String -> Ontology
             -> (OntologyMap, DGraph)
             -> (OntologyMap, DGraph)
graphFromMap uri onto (ontoMap, dg) =
    let existedLNodes = labNodesDG dg
        currentSign = simpleSign $ QN "" uri ""
       -- get current node
        (lnode, ontoMap1) =
            createLNodes [uri] existedLNodes ontoMap
        cl@(ind, _) = head lnode
        importsList = searchImports onto
       -- create LabNodes from imports list, thsi incl. the LNodes which been
       -- existed because of building of edge.
        (tagLNodes, ontoMap2) =
            createLNodes importsList (nub (cl:existedLNodes)) ontoMap1
       -- if tagnode existed then it muss be reduced.
        newLNodes = reduceLNodes (cl:tagLNodes) dg

        morphism = idComorphism (Logic OWL_DL)
        Result _ (Just comorphism) =
             gEmbedComorphism morphism (G_sign OWL_DL currentSign 0)

        -- to add ids into edges
        ledgeList = zipWith (\(indT, _) n ->
                                (ind, indT, DGLink{ dgl_morphism = comorphism
                                                  , dgl_type = GlobalDef
                                                  , dgl_origin = DGImports
                                                  , dgl_id = [n]
                                                  }))
                            tagLNodes
                            (getNewEdgeIDs (length tagLNodes) dg)
    in (ontoMap2, insEdgesDG ledgeList (insNodesDG newLNodes dg))


searchImports :: Ontology -> [String]
searchImports (Ontology _ directives _) = findImports directives
    where
    findImports :: [Directive] -> [String]
    findImports [] = []
    findImports (hd:rd) =
        case hd of
        Ax (OntologyProperty oid uriannos) ->
            if localPart oid == "imports" then
               findImports' uriannos
               else findImports rd
        _ -> findImports rd
    findImports' :: [OWL_DL.AS.Annotation] -> [String]
    findImports' [] = []
    findImports' (ha:ra) =
        case ha of
        URIAnnotation _ qn ->
            (localPart qn):(findImports' ra)
        _ -> []

createLNodes :: [String] -> [LNode DGNodeLab]
             -> OntologyMap
             -> ([LNode DGNodeLab], OntologyMap)
createLNodes [] _ om = ([], om)
createLNodes (hs:rs) exLNodes om =
    let lnode@(_, currentLN) = buildLNodeFromStr hs ((length exLNodes)-1)
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
                    (sid, _, _) = dgn_name $ snd lnode'
                in
                   (
                     lnode':newLNodes,
                     Map.delete hs (Map.insert (show sid)
                                    (case Map.lookup hs ontoMap' of
                                      Just res -> res
                                      Prelude.Nothing -> emptyOntology
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
            let name@(sid, u1, u2) = dgn_name dgn
                nameSet = map (dgn_name . snd) exn
                name' = if name `elem` nameSet then
                           let n = show sid
                               nsid = if isDigit $ head $ reverse n then
                                         take ((length n) - 1) n
                                         else n
                           in  fromJust $ find (not . flip elem nameSet)
                                   [(mkSimpleId (nsid ++
                                            (show (i::Int))),u1,u2)|i<-[1..]]
                         else name
            in  (ind, dgn {dgn_name = name'})

buildLNodeFromStr :: String -> Int -> (LNode DGNodeLab)
buildLNodeFromStr uri i =
    let name = uriToName uri
        nodeName = makeName $ mkSimpleId name
        currentSign = simpleSign $ QN "" uri ""
    in  (i+1, newNodeLab nodeName DGBasic $ noSensGTheory OWL_DL currentSign 0)

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
                                Prelude.Nothing -> emptyOntology
                         ) dgnNames
        newName = makeName $ mkSimpleId $ (\z -> take ((length z) -1) z) $
                    foldr (\x y -> x ++ "_" ++ y) "" dgnNames
        newTheory = integrateTheory theories
        newNodeNum = noNodesDG dg
    in ( Map.insert (getNameFromNode newName)
                    (foldl integrateOntology emptyOntology ontologies)
                    (Map.filterWithKey (\x _ -> not $ x `elem` dgnNames)
                     ontoMap)
       , delNodesDG nodeList $ changeEdges decomps newNodeNum $ insNodeDG
             (newNodeNum, newNodeLab newName DGintegratedSCC newTheory) dg)

-- simple integrate Theory
integrateTheory :: [G_theory] -> G_theory
integrateTheory theories =
  foldl assembleTheories emptyOWL_DLTheory theories
   where
    assembleTheories :: G_theory -> G_theory -> G_theory
    assembleTheories (G_theory lid1 sign1 _ theSen1 _)
                     (G_theory lid2 sign2 _ theSen2 _) =
              let thSen2' = maybe (error "could not coerce sentences")
                        id (coerceThSens lid2 lid1 "" theSen2)
                  sign2' = maybe (error "could not coerce sign")
                        id (coerceSign lid2 lid1 "" sign2)
                  csign = case signature_union lid1 sign2' sign1 of
                          Result dgs mv ->
                              maybe (error ("sig_union"++show dgs)) id mv
              in G_theory lid1 csign 0 (joinSens theSen1 thSen2') 0

getNameFromNode :: NODE_NAME -> String
getNameFromNode (sid, _, _) = show sid

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

emptyOWL_DLTheory:: G_theory
emptyOWL_DLTheory = noSensGTheory OWL_DL emptySign 0
