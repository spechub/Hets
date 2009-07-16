{- |
Module      :  $Header$
Description :  heterogeneous signatures colimits approximations
Copyright   :  (c) Mihai Codescu, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  mcodescu@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

Heterogeneous version of weakly_amalgamable_cocones.
Needs some improvements (see TO DO).

-}

module Static.WACocone(isConnected,
                       isAcyclic,
                       isThin,
                       removeIdentities,
                       hetWeakAmalgCocone,
                       initDescList,
                       dijkstra,
                       buildStrMorphisms,
                       weakly_amalgamable_colimit
                       ) where

import Control.Monad
import Data.List(nub)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Graph.Inductive.Graph as Graph

import Common.Lib.Graph as Tree
import Common.ExtSign
import Common.Result
import Common.LogicT

import Logic.Logic
import Logic.Comorphism
import Logic.Modification
import Logic.Grothendieck
import Logic.Coerce
import Static.GTheory
import Comorphisms.LogicGraph

weakly_amalgamable_colimit :: StaticAnalysis lid
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol
    => lid -> Tree.Gr sign (Int, morphism)
           -> Result (sign, Map.Map Int morphism)
weakly_amalgamable_colimit l diag = do
          (sig, sink) <- signature_colimit l diag
          return (sig, sink)
-- until amalgamability check is fixed, just return a colimit
-- get (commented out) code from rev:11881

-- | checks whether a graph is connected

isConnected :: Gr a b -> Bool
isConnected graph = let
  nodeList = nodes graph
  root = head nodeList
  availNodes = Map.fromList $ zip nodeList (repeat True)
  bfs queue avail = case queue of
     [] -> avail
     n:ns -> let
       avail1 = Map.insert n False avail
       nbs = filter (\x -> Map.findWithDefault (error "isconnected") x avail)
             $ neighbors graph n
      in bfs (ns++nbs) avail1
  in filter (\x -> Map.findWithDefault (error "iscon 2") x
                   (bfs [root] availNodes)) nodeList == []

-- | checks whether the graph is thin

isThin :: Gr a b -> Bool
isThin graph = checkThinness (Map.empty) $ edges graph

checkThinness :: Map.Map Edge Int -> [Edge] -> Bool
checkThinness paths eList =
  case eList of
   [] -> True
   (sn,tn):eList' ->
      if (sn,tn) `elem` (Map.keys paths) then
         False -- multiple paths between (sn, tn)
      else
      let pathsToS = filter (\(_,y) -> y == sn) $ Map.keys paths
          updatePaths pathF dest pList =
            case pList of
              [] -> Just pathF
              (x,_):pList' ->
                if (x,dest) `elem` (Map.keys pathF) then Nothing
                else updatePaths (Map.insert (x,dest) 1 pathF) dest pList'
      in case updatePaths paths tn pathsToS of
            Nothing -> False
            Just paths' -> checkThinness (Map.insert (sn,tn) 1 paths') eList'


-- | checks whether a graph is acyclic

isAcyclic :: (Eq b) => Gr a b -> Bool
isAcyclic graph = let
  filterIns gr = filter (\ x -> indeg gr x == 0)
  queue = filterIns graph $ nodes graph
  topologicalSort q gr = case q of
   [] -> null $ edges gr
   n : ns -> let
     oEdges = lsuc gr n
     graph1 = foldl (flip Graph.delLEdge) gr
              $ map (\ (y, label) -> (n, y, label)) oEdges
     succs = filterIns graph1 $ suc gr n
    in topologicalSort (ns ++ succs) graph1
 in topologicalSort queue graph

-- | auxiliary for removing the identity edges from a graph

removeIdentities :: Gr a b -> Gr a b
removeIdentities graph = let
 addEdges gr eList = case eList of
   [] -> gr
   (sn, tn, label):eList1 -> if sn == tn then addEdges gr eList1
                             else addEdges (insEdge (sn, tn, label) gr) eList1
 in (addEdges $ insNodes (labNodes graph) Graph.empty)
        $ labEdges graph

--  assigns to a node all proper descendents
initDescList :: (Eq a, Eq b) => Gr a b -> Map.Map Node [(Node, a)]
initDescList graph =  let
 descsOf n = let
  nodeList = filter (\x -> x /= n) $ pre graph n
  f = Map.fromList $ zip nodeList (repeat False)
  precs nList nList' avail =
    case nList of
      [] -> nList'
      _ -> let
            nList'' = concat $
                      map (\y -> filter (\x -> if x `elem` Map.keys avail
                                                then
                                               Map.findWithDefault (error "iDL")
                                                x avail
                                                else True ) $
                                 filter (\x -> x /= y) $
                                 pre graph y) nList
            avail' = Map.union avail $
                     Map.fromList $ zip nList'' (repeat False)
           in precs (nub nList'') (nub $ nList' ++ nList'') avail'
             in precs nodeList nodeList f
  in Map.fromList$ map (\node -> (node, filter (\x->(fst x) `elem`
                                                   descsOf node)
                                       $ labNodes graph )) $ nodes graph

commonBounds :: (Eq a) => Map.Map Node [(Node, a)] -> Node -> Node -> [(Node,a)]
commonBounds funDesc n1  n2 = filter
  (\x -> x `elem` ((Map.!) funDesc n1) && x `elem` ((Map.!) funDesc n2) )
  $ nub $ (Map.!) funDesc n1 ++ (Map.!) funDesc n2

--  returns the greatest lower bound of two maximal nodes,if it exists
glb :: (Eq a) =>  Map.Map Node [(Node, a)] -> Node -> Node -> Maybe (Node,a)
glb funDesc n1 n2 = let
 cDescs = commonBounds funDesc n1 n2
 subList [] _ = True
 subList (x:xs) l2 = x `elem` l2 && subList xs l2
 glbList = filter (\(n, x) -> subList
    (filter (\(n0,x0) -> (n,x)/= (n0,x0)) cDescs) (funDesc Map.! n)
           ) cDescs
    -- a node n is glb of n1 and n2 iff
    -- all common bounds of n1 and n2 are also descendants of n
  in case glbList of
     [] -> Nothing
     x:_ -> Just x -- because if it exists, there can be only one

-- if no greatest lower bound exists, compute all maximal bounds of the nodes
maxBounds :: (Eq a) => Map.Map Node [(Node, a)] -> Node -> Node -> [(Node, a)]
maxBounds funDesc n1 n2 = let
  cDescs = commonBounds funDesc n1 n2
  isDesc n0 (n,y) = (n,y) `elem` funDesc Map.! n0
  noDescs (n,y) = filter (\(n0, _) -> isDesc n0 (n,y)) cDescs == []
 in filter noDescs cDescs

--  dijsktra algorithm for finding the the shortest path between two nodes
dijkstra :: GDiagram -> Node -> Node -> Result GMorphism
dijkstra graph source target = do
 let
  dist = Map.insert source 0 $ Map.fromList $
         zip (nodes graph) $ repeat $  2 * (length $ edges graph)
  prev = if source == target then Map.insert source source Map.empty
         else Map.empty
  q = nodes graph
  com = case lab graph source of
    Nothing -> Map.empty --shouldnt be the case
    Just gt -> Map.insert source (ide $ signOf gt) Map.empty
  extractMin queue dMap = let
   u =  head $
     filter (\x -> Map.findWithDefault (error "dijkstra") x dMap ==
             (minimum $
               map (\x1 -> Map.findWithDefault (error "dijkstra") x1 dMap)
               queue))
               queue
   in ( Set.toList $ Set.difference (Set.fromList queue) (Set.fromList [u]) , u)
  updateNeighbors d p c u gr = let
    outEdges = out gr u
    upNeighbor dMap pMap cMap uNode edgeList = case edgeList of
     [] -> (dMap, pMap, cMap)
     (_, v, (_, gmor)):edgeL  -> let
       alt = ( Map.findWithDefault (error "dijkstra") uNode dMap) + 1
      in
        if (alt >= Map.findWithDefault (error "dijsktra") v dMap) then
          upNeighbor dMap pMap cMap uNode edgeL
        else let
      d1 = Map.insert v alt dMap
      p1 = Map.insert v uNode pMap
      c1 = Map.insert v gmor cMap
      in upNeighbor d1 p1 c1 uNode edgeL
   in upNeighbor d p c u outEdges
  -- for each neighbor of u, if d(u)+1 < d(v), modify p(v) = u, d(v) = d(u)+1
  mainloop gr sn tn qL d p c = let
   (q1, u) =  extractMin qL d
   (d1, p1, c1) = updateNeighbors d p c u gr
   in if (u == tn) then shortPath sn p1 c1 [] tn
     else mainloop gr sn tn q1 d1 p1 c1
  shortPath sn p1 c s u =
   if not $ u `elem` Map.keys p1 then fail "path not found"
    else let
    x = Map.findWithDefault (error $ show u) u p1 in
    if x == sn then return (u:s, c)
     else shortPath sn p1 c (u:s) x
 (nodeList, com1) <- mainloop graph source target q dist prev com
 foldM comp ((Map.!) com1 source) . map ((Map.!) com1) $ nodeList

--  builds the arrows from the nodes of the original graph
--  to the unique maximal node of the obtained graph

buildStrMorphisms ::  GDiagram -> GDiagram
                    ->Result (G_theory, Map.Map Node GMorphism)
buildStrMorphisms initGraph newGraph = do
 let (maxNode, sigma) = head $ filter (\(node,_) -> outdeg newGraph node == 0) $
                        labNodes newGraph
     buildMor pairList solList = do
      case pairList of
       (n, _):pairs -> do  nMor <- dijkstra newGraph n maxNode
                           buildMor pairs (solList ++ [(n,nMor)])
       [] -> return solList
 morList <- buildMor (labNodes initGraph) []
 return $ (sigma, Map.fromList morList)

--  computes the colimit and inserts it into the graph
addNodeToGraph :: GDiagram -> G_theory -> G_theory -> G_theory -> Int -> Int
               -> Int -> GMorphism -> GMorphism
               -> Map.Map Node [(Node, G_theory)] -> [(Int, G_theory)]
               -> Result (GDiagram, Map.Map Node [(Node, G_theory)])
addNodeToGraph oldGraph
               (G_theory lid extSign _ _ _)
               gt1@(G_theory lid1 extSign1 idx1 _ _)
               gt2@(G_theory lid2 extSign2 idx2 _ _)
               n
               n1
               n2
               (GMorphism cid1 ss1  _ mor1 _)
               (GMorphism cid2 ss2  _ mor2 _)
               funDesc maxNodes = do
 let newNode = 1 + (maximum $ nodes oldGraph) --get a new node
 s1 <- coerceSign lid1 lid "addToNodeGraph" extSign1
 s2 <- coerceSign lid2 lid "addToNodeGraph" extSign2
 m1 <- coerceMorphism (targetLogic cid1) lid "addToNodeGraph" mor1
 m2 <- coerceMorphism (targetLogic cid2) lid "addToNodeGraph" mor2
 let spanGr = Graph.mkGraph
       [(n, plainSign extSign), (n1, plainSign s1), (n2, plainSign s2)]
       [(n, n1, (1, m1)), (n, n2, (1, m2))]
 (sig,morMap) <- weakly_amalgamable_colimit lid spanGr
      -- must  coerce here
 m11 <- coerceMorphism lid (targetLogic cid1) "addToNodeGraph" $
        morMap Map.! n1
 m22 <- coerceMorphism lid (targetLogic cid2) "addToNodeGraph" $
        morMap Map.! n2
 let gth = noSensGTheory lid (mkExtSign sig) startSigId
     gmor1 = GMorphism cid1 ss1 idx1 m11 startMorId
     gmor2 = GMorphism cid2 ss2 idx2 m22 startMorId
 case maxNodes of
   [] -> do
    let newGraph = insEdges [(n1, newNode,(1, gmor1)),(n2, newNode,(1,gmor2))] $
                   insNode (newNode, gth) oldGraph
        funDesc1 = Map.insert newNode
                     (nub $ (Map.!)funDesc n1 ++ (Map.!) funDesc n2 ) funDesc
    return (newGraph, funDesc1)
   _ -> computeCoeqs oldGraph funDesc (n1, gt1) (n2, gt2)
                           (newNode, gth) gmor1 gmor2 maxNodes

--  for each node in the list, check whether the coequalizer can be computed
--  if so, modify the maximal node of graph and the edges to it from n1 and n2
computeCoeqs :: GDiagram -> Map.Map Node [(Node, G_theory)]
                   ->  (Node,G_theory) -> (Node,G_theory) -> (Node, G_theory)
                   ->  GMorphism -> GMorphism -> [(Node, G_theory)]->
                       Result (GDiagram, Map.Map Node [(Node, G_theory)])
computeCoeqs oldGraph funDesc (n1,_) (n2,_) (newN, newGt) gmor1 gmor2 [] = do
 let newGraph = insEdges [(n1, newN, (1, gmor1)),(n2, newN, (1, gmor2))] $
                insNode (newN, newGt) oldGraph
     descFun1 = Map.insert newN
                (nub $ (Map.!)funDesc n1 ++ (Map.!) funDesc n2 ) funDesc
 return $ (newGraph, descFun1)
computeCoeqs graph funDesc (n1,gt1) (n2,gt2)
                    (newN, _newGt@(G_theory tlid tsign _ _ _))
                    _gmor1@(GMorphism cid1 sig1 idx1 mor1 _ )
                    _gmor2@(GMorphism cid2 sig2 idx2 mor2 _ ) ((n,gt):descs)= do
 _rho1@(GMorphism cid3 _ _ mor3 _)<- dijkstra graph n n1
 _rho2@(GMorphism cid4 _ _ mor4 _)<- dijkstra graph n n2
 com1 <- compComorphism (Comorphism cid1) (Comorphism cid3)
 com2 <- compComorphism (Comorphism cid1) (Comorphism cid3)
 if com1 /= com2 then  fail "Unable to compute coequalizer" else do
   _gtM@(G_theory lidM signM _idxM _ _)<- mapG_theory com1 gt
   s1 <- coerceSign lidM tlid "coequalizers" signM
   mor3' <- coerceMorphism (targetLogic cid3) (sourceLogic cid1) "coeqs" mor3
   mor4' <- coerceMorphism (targetLogic cid4) (sourceLogic cid2) "coeqs" mor4
   m1 <- map_morphism cid1 mor3'
   m2 <- map_morphism cid2 mor4'
   phi1' <- comp m1 mor1
   phi2' <- comp m2 mor2
   phi1 <- coerceMorphism (targetLogic cid1) tlid "coeqs" phi1'
   phi2 <- coerceMorphism (targetLogic cid2) tlid "coeqs" phi2'
   -- build the double arrow for computing the coequalizers
   let doubleArrow = Graph.mkGraph
         [(n, plainSign s1), (newN, plainSign tsign)]
         [(n, newN, (1, phi1)), (n, newN, (1, phi2))]
   (colS, colM) <- weakly_amalgamable_colimit tlid doubleArrow
   let newGt1 = noSensGTheory tlid (mkExtSign colS) startSigId
   mor11' <- coerceMorphism tlid (targetLogic cid1) "coeqs" $ (Map.!) colM newN
   mor11 <- comp mor1 mor11'
   mor22' <- coerceMorphism tlid (targetLogic cid2) "coeqs" $ (Map.!) colM newN
   mor22 <- comp mor2 mor22'
   let gMor11 = GMorphism cid1 sig1 idx1 mor11 startMorId
   let gMor22 = GMorphism cid2 sig2 idx2 mor22 startMorId
   computeCoeqs graph funDesc (n1, gt1) (n2,gt2) (newN, newGt1)
                       gMor11 gMor22 descs

--  returns a maximal node available
pickMaxNode :: (MonadPlus t) => Gr a b -> t (Node,a)
pickMaxNode graph = msum $ map return $
                    filter (\(node,_) -> outdeg graph node == 0) $
                    labNodes graph

--  returns a list of common descendants of two maximal nodes:
--  one node if a glb exists, or all maximal descendants otherwise
commonDesc ::  Map.Map Node [(Node,G_theory)] -> Node -> Node
            -> [(Node, G_theory)]
commonDesc funDesc n1 n2 = case glb funDesc n1 n2 of
                            Just x -> [x]
                            Nothing -> maxBounds funDesc n1 n2

-- returns a weakly amalgamable square of lax triangles
pickSquare :: (MonadPlus t) => Result GMorphism -> Result GMorphism -> t Square
pickSquare (Result _ (Just phi1@(GMorphism cid1 _ _ _ _)))
           (Result _ (Just phi2@(GMorphism cid2 _ _ _ _))) =
   if (isHomogeneous phi1 && isHomogeneous phi2) then
      return $ mkIdSquare $ Logic $ sourceLogic cid1
    --since they have the same target, both homogeneous implies same logic
   else do
    -- if one of them is homogeneous, build the square
    -- with identity modification of the other comorphism
    let defaultSquare = if isHomogeneous phi1 then
                           [mkDefSquare $ Comorphism cid2]
                        else if isHomogeneous phi2 then
                                 [mirrorSquare $ mkDefSquare $ Comorphism cid1]
                             else []
    case maybeResult $ lookupSquare_in_LG (Comorphism cid1)(Comorphism cid2) of
          Nothing -> msum $ map return $  defaultSquare
          Just sqList -> msum $ map return $ sqList ++ defaultSquare

pickSquare (Result _ Nothing) _ = fail "Error computing comorphisms"
pickSquare _ (Result _ Nothing) = fail "Error computing comorphisms"

--  builds the span for which the colimit is computed
buildSpan :: GDiagram ->
             Map.Map Node [(Node, G_theory)] ->
             AnyComorphism ->
             AnyComorphism ->
             AnyComorphism ->
             AnyComorphism ->
             AnyComorphism ->
             AnyModification ->
             AnyModification ->
             G_theory ->
             G_theory ->
             G_theory ->
             GMorphism ->
             GMorphism ->
             Int -> Int -> Int ->
             [(Int, G_theory)]->
             Result (GDiagram, Map.Map Node [(Node,G_theory)])
buildSpan graph
          funDesc
          d@(Comorphism _cidD)
          e1@(Comorphism cidE1)
          e2@(Comorphism cidE2)
          _d1@(Comorphism _cidD1)
          _d2@(Comorphism _cidD2)
          _m1@(Modification cidM1)
          _m2@(Modification cidM2)
          gt@(G_theory lid sign _ _ _)
          gt1@(G_theory lid1 sign1 _ _ _)
          gt2@(G_theory lid2 sign2 _ _ _)
          _phi1@(GMorphism cid1 _  _ mor1 _)
          _phi2@(GMorphism cid2 _  _ mor2 _)
          n n1 n2
          maxNodes
           =  do
 sig@(G_theory _lid0 _sign0 _ _ _)  <-  mapG_theory d gt -- phi^d(Sigma)
 sig1 <- mapG_theory e1 gt1 -- phi^e1(Sigma1)
 sig2 <- mapG_theory e2 gt2 -- phi^e2(Sigma2)
 mor1' <- coerceMorphism (targetLogic cid1) (sourceLogic cidE1) "buildSpan" mor1
 eps1 <- map_morphism cidE1 mor1' -- phi^e1(sigma1)
 sign' <- coerceSign lid (sourceLogic$ sourceComorphism cidM1) "buildSpan" sign
 tau1 <- tauSigma cidM1 (plainSign sign') -- I^u1_Sigma
 tau1' <- coerceMorphism (targetLogic$ sourceComorphism cidM1)
                         (targetLogic cidE1) "buildSpan" tau1
 rho1 <- comp tau1' eps1
 mor2' <- coerceMorphism (targetLogic cid2) (sourceLogic cidE2) "buildSpan" mor2
 eps2 <- map_morphism cidE2 mor2' --phi^e2(sigma2)
 sign'' <- coerceSign lid (sourceLogic$ sourceComorphism cidM2) "buildSpan" sign
 tau2 <- tauSigma cidM2 (plainSign sign'') -- I^u2_Sigma
 tau2' <- coerceMorphism (targetLogic$ sourceComorphism cidM2)
                         (targetLogic cidE2) "buildSpan" tau2
 rho2 <- comp tau2' eps2
 signE1 <- coerceSign lid1 (sourceLogic cidE1) " " sign1
 signE2 <- coerceSign lid2 (sourceLogic cidE2) " " sign2
 (graph1, funDesc1) <- addNodeToGraph graph sig sig1 sig2 n n1 n2
     (GMorphism cidE1 signE1 startSigId rho1 startMorId)
     (GMorphism cidE2 signE2 startSigId rho2 startMorId)
     funDesc maxNodes
 return (graph1, funDesc1)

pickMaximalDesc :: (MonadPlus t) => [(Node, G_theory)] -> t (Node, G_theory)
pickMaximalDesc descList = msum$ map return descList

nrMaxNodes :: Gr a b -> Int
nrMaxNodes graph = length $ filter (\n -> outdeg graph n == 0) $ nodes graph

-- | backtracking function for heterogeneous weak amalgamable cocones
hetWeakAmalgCocone :: (Monad m, LogicT t, MonadPlus (t m)) =>
                     GDiagram -> Map.Map Int [(Int, G_theory)] -> t m GDiagram
hetWeakAmalgCocone graph funDesc =
 if nrMaxNodes graph  == 1 then return graph
 else once $ do
  (n1,gt1) <- pickMaxNode graph
  (n2,gt2) <- pickMaxNode graph
  guard (n1 < n2) -- to consider each pair of maximal nodes only once
  let descList = commonDesc funDesc n1 n2
  case length descList of
    0 -> mzero -- no common descendants for n1 and n2
    _ -> do -- just one common descendant implies greatest lower bound
            --  for several, the tail is not empty and we compute coequalizers
     (n,gt) <- pickMaximalDesc descList
     let phi1 =  dijkstra graph n n1
         phi2 =  dijkstra graph n n2
     square <-  pickSquare phi1 phi2
     let d  = laxTarget $ leftTriangle square
         e1 = laxFst $ leftTriangle square
         d1 = laxSnd $ leftTriangle square
         e2 = laxFst $ rightTriangle square
         d2 = laxSnd $ rightTriangle square
         m1 = laxModif $ leftTriangle square
         m2 = laxModif $ rightTriangle square
     case maybeResult phi1 of
      Nothing -> mzero
      Just phi1' -> case maybeResult phi2 of
       Nothing -> mzero
       Just phi2' -> do
        let mGraph = buildSpan graph funDesc d e1 e2 d1 d2 m1 m2 gt gt1 gt2
                      phi1' phi2' n n1 n2 $ filter (\(nx,_) -> nx /=n) descList
        case  maybeResult mGraph  of
         Nothing -> mzero
         Just (graph1, funDesc1) -> hetWeakAmalgCocone graph1 funDesc1
