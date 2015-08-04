{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2004-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(uni)

displays an ontology graph
-}

module Taxonomy.MMiSSOntologyGraph (displayClassGraph) where

import Data.List
import Control.Monad
import Data.IORef

import GUI.UDGUtils
import qualified GUI.HTkUtils as S
import Taxonomy.MMiSSOntology

import qualified Data.Map as Map
import Common.Lib.Graph
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Query.DFS
import qualified Data.Foldable

import qualified Taxonomy.AbstractGraphView as A

displayClassGraph :: MMiSSOntology -> Maybe String -> IO A.OurGraph
displayClassGraph onto startClass = do
    S.initHTk []
    ginfo <- A.initgraphs
    classGraph <- case startClass of
        Nothing -> return $ getPureClassGraph $ getClassGraph onto
        Just className -> case gselName className $ getClassGraph onto of
            [] -> return $ getPureClassGraph $ getClassGraph onto
            (_, v, l, _) : _ -> return $ ([], v, l, []) & empty
    A.Result gid _ <-
       A.makegraph (getOntologyName onto) Nothing Nothing Nothing
           [GlobalMenu (Button "Button2" (putStrLn "Button2 was pressed"))]
           (map ( \ ( nam, col) -> (getTypeLabel nam, Box $$$ Color col $$$
                 createLocalMenu onto ginfo
                 $$$ ValueTitle ( \ (name, _, _) -> return name) $$$
                 emptyNodeTypeParms :: DaVinciNodeTypeParms (String, Int, Int)
                 )) [ (OntoClass, "#e0eeee")
                    , (OntoPredicate, "#ffd300")
                    , (OntoObject, "#ffffA0") ])
           (createEdgeTypes $ getClassGraph onto)
           []
           ginfo
    updateDaVinciGraph classGraph gid ginfo
    setEmptyRelationSpecs gid ginfo onto
    A.Result gid' _ <- A.redisplay gid ginfo
    A.getGraphid gid' ginfo

setEmptyRelationSpecs :: A.Descr -> A.GraphInfo -> MMiSSOntology -> IO ()
setEmptyRelationSpecs gid gv onto = do
    (gs, _) <- readIORef gv
    case lookup gid gs of
      Nothing -> return ()
      _ -> do
          A.writeRelViewSpecs gid
               (map ( \ relname -> A.RelViewSpec relname False False)
               $ getRelationNames onto) gv
          return ()

updateDaVinciGraph :: Gr (String, String, OntoObjectType) String -> A.Descr
                   -> A.GraphInfo -> IO ()
updateDaVinciGraph nGraph gid gv = do
    (gs, _) <- readIORef gv
    case lookup gid gs of
      Nothing -> return ()
      Just g -> do
           let oldGraph = A.ontoGraph g
               nMap = A.nodeMap g
           nodeMap1 <- foldM (createNode gid gv oldGraph) nMap
               $ labNodes nGraph
           nodeMap2 <- foldM (createLink gid gv) nodeMap1 $ labEdges nGraph
           A.Result gid' err <- A.writeOntoGraph gid nGraph gv
           A.writeNodeMap gid' nodeMap2 gv
           Data.Foldable.forM_ err putStr

getTypeLabel :: OntoObjectType -> String
getTypeLabel t = case t of
    OntoClass -> "class"
    OntoObject -> "object"
    OntoPredicate -> "predicate"

createNode :: Int -> A.GraphInfo -> ClassGraph -> A.NodeMapping
           -> LNode (String, String, OntoObjectType) -> IO A.NodeMapping
createNode gid ginfo _ nMap (nodeID, (name, _, objectType)) =
            case Map.lookup nodeID nMap of
              Just _ -> return nMap
              Nothing ->
                do A.Result nid err <-
                       A.addnode gid (getTypeLabel objectType) name ginfo
                   case err of
                     Nothing -> return (Map.insert nodeID nid nMap)
                     Just str -> do
                         putStr str
                         return $ Map.insert nodeID nid nMap

createLink :: A.Descr -> A.GraphInfo -> A.NodeMapping -> LEdge String
           -> IO A.NodeMapping
createLink gid ginfo nMap (node1, node2, edgeLabel) = do
    dNodeID_1 <- case Map.lookup node1 nMap of
                   Nothing -> return (-1)
                   Just n -> return n
    dNodeID_2 <- case Map.lookup node2 nMap of
                   Nothing -> return (-1)
                   Just n -> return n
    if dNodeID_1 == -1 || dNodeID_2 == -1 then return nMap else do
      A.Result _ err <-
        if elem edgeLabel ["isa", "instanceOf", "livesIn", "proves"]
        then A.addlink gid edgeLabel edgeLabel Nothing
             dNodeID_2 dNodeID_1 ginfo
        else A.addlink gid edgeLabel edgeLabel Nothing
             dNodeID_1 dNodeID_2 ginfo
      Data.Foldable.forM_ err putStr
      return nMap

showRelationsForVisible :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int)
                        -> IO ()
showRelationsForVisible onto gv (_, _, gid) =
  do (gs, _) <- readIORef gv
     case lookup gid gs of
       Nothing -> return ()
       Just g ->
         do let oldGraph = A.ontoGraph g
                nodesInOldGraph = map fst $ labNodes oldGraph
                newGr = restrict (`elem` nodesInOldGraph) $ getClassGraph onto
            purgeGraph gid gv
            updateDaVinciGraph newGr gid gv
            A.redisplay gid gv
            return ()

showObjectsForVisible :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int)
                      -> IO ()
showObjectsForVisible onto gv (_, _, gid) =
  do (gs, _) <- readIORef gv
     case lookup gid gs of
       Nothing -> return ()
       Just g ->
         do let oldGraph = A.ontoGraph g
                classesInOldGraph =
                    map ( \ (_, _, (className, _, _), _) -> className)
                    $ filter ( \ (_, _, (_, _, objectType), _)
                                   -> objectType == OntoClass)
                    $ map (context oldGraph) $ nodes oldGraph

                findObjectsOfClass classList (_, (_, className, _)) =
                    elem className classList
                objectList =
                    map fst $ filter (findObjectsOfClass classesInOldGraph)
                    $ getTypedNodes [OntoObject] $ getClassGraph onto
                objectGr = restrict (`elem` objectList) (getClassGraph onto)
            updateDaVinciGraph (makeObjectGraph oldGraph
                                (getPureClassGraph (getClassGraph onto))
                                objectGr) gid gv
            A.redisplay gid gv
            return ()

showWholeObjectGraph :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int)
                     -> IO ()
showWholeObjectGraph onto gv (_, _, gid) =
  do oldGv <- readIORef gv
     A.Result _ err <- purgeGraph gid gv
     let objectList = map fst $ getTypedNodes [OntoObject] $ getClassGraph onto
         objectGraph = restrict (`elem` objectList) $ getClassGraph onto
     updateDaVinciGraph (makeObjectGraph empty
                         (getClassGraph onto) objectGraph) gid gv
     case err of
       Just _ -> writeIORef gv oldGv
       Nothing -> do
           A.redisplay gid gv
           return ()

makeObjectGraph :: ClassGraph -> ClassGraph -> ClassGraph -> ClassGraph
makeObjectGraph oldGr classGr objectGr =
  let newGr = insNodes (labNodes objectGr) oldGr
      newGr2 = foldl insEdgeSecurely newGr (labEdges objectGr)
      newGr3 = foldl insInstanceOfEdge newGr2 (labNodes objectGr)
  in newGr3
  where
    insEdgeSecurely gr (node1, node2, label) = case match node1 gr of
        (Nothing, _) -> gr
        _ -> case match node2 gr of
            (Nothing, _) -> gr
            _ -> insEdge (node1, node2, label) gr
    insInstanceOfEdge gr (_, (objectName, className, _)) =
      case findLNode gr className of
        Nothing -> case findLNode classGr className of
          Nothing -> gr
          Just classNodeID -> insInstanceOfEdge1
              (insNode (classNodeID, (className, "", OntoClass)) gr)
                                            classNodeID objectName
        Just classNodeID -> insInstanceOfEdge1 gr classNodeID objectName
    insInstanceOfEdge1 gr classNodeID objectName =
      case findLNode gr objectName of
        Nothing -> gr
        Just objectNodeID -> insEdge
             (objectNodeID, classNodeID, "instanceOf") gr

showWholeClassGraph :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int)
                    -> IO ()
showWholeClassGraph onto gv (_, _, gid) =
  do oldGv <- readIORef gv
     A.Result _ err <- purgeGraph gid gv
     updateDaVinciGraph (getPureClassGraph (getClassGraph onto)) gid gv
     case err of
       Just _ -> writeIORef gv oldGv
       Nothing -> do
         A.redisplay gid gv
         return ()

showRelationsToNeighbors :: MMiSSOntology -> A.GraphInfo -> [String]
                         -> (String, Int, Int) -> IO ()
showRelationsToNeighbors onto gv rels (name, _, gid) =
  do oldGv <- readIORef gv
     updateDaVinciGraph (reduceToNeighbors (getClassGraph onto)
                         name rels) gid gv
     writeIORef gv oldGv

reduceToNeighbors :: ClassGraph -> String -> [String] -> ClassGraph
reduceToNeighbors g name forbiddenRels =
  case findLNode g name of
    Nothing -> g
    Just node ->
      let (p, v, l, s) = context g node
          noForbidden = not . (`elem` forbiddenRels) . fst
          p' = filter noForbidden p
          s' = filter noForbidden s
          ns = map snd p' ++ map snd s'
          myInsNode gr newGr nodeID = case match nodeID newGr of
              (Nothing, _) ->
                  ([], nodeID, lab' (context gr nodeID), []) & newGr
              _ -> newGr
      in (p', v, l, s') & foldl (myInsNode g) empty ns

showAllRelations :: MMiSSOntology -> A.GraphInfo -> Bool -> [String]
                 -> (String, Int, Int) -> IO ()
showAllRelations onto gv withIncoming rels (name, _, gid) =
  do oldGv <- readIORef gv
     let newGr = reduceToRelations (getClassGraph onto)
                  empty withIncoming rels name
     updateDaVinciGraph newGr gid gv
     writeIORef gv oldGv

reduceToRelations :: ClassGraph -> ClassGraph -> Bool -> [String] -> String
                  -> ClassGraph
reduceToRelations wholeGraph g withIncoming forbiddenRels name =
  let g1 = elfilter (not . (`elem` forbiddenRels)) wholeGraph
  in case findLNode g1 name of
       Nothing -> g
       Just selectedNode ->
          let nodeList = if withIncoming
                           then udfs [selectedNode] g1
                           else dfs [selectedNode] g1
              toDelete = nodes g1 \\ nodeList
              g1' = delNodes toDelete g1
              g2 = mergeGraphs g1' g
              newNodesList = nodeList \\ nodes g
          in if null newNodesList
               then g2
               else foldl (followRelationOverSubClasses wholeGraph
                           withIncoming forbiddenRels) g2 newNodesList

followRelationOverSubClasses :: ClassGraph -> Bool -> [String] -> ClassGraph
                             -> Node -> ClassGraph
followRelationOverSubClasses wholeGraph withIncoming forbiddenRels g node =
 let g1 = elfilter (== "isa") wholeGraph
 in case match node g1 of
      (Nothing, _) -> g
      _ ->
         let subclasses = rdfs [node] g1
             newNs = subclasses \\ nodes g
         in if null newNs
              then g
              else
                let
                  toDelete = nodes g1 \\ subclasses
                  g2 = mergeGraphs (delNodes toDelete g1) g
                in foldl transClosureForNode g2 newNs
 where
   transClosureForNode g' n =
     let (name, _, _) = lab' $ context wholeGraph n
     in reduceToRelations wholeGraph g' withIncoming forbiddenRels name

mergeGraphs :: ClassGraph -> ClassGraph -> ClassGraph
mergeGraphs g1 g2 =
  insEdges (labEdges g2) $ insNodes (labNodes g2 \\ labNodes g1) g1

showSuperSubClassesForVisible :: MMiSSOntology -> A.GraphInfo -> Bool -> Bool
                              -> (String, Int, Int) -> IO ()
showSuperSubClassesForVisible onto gv showSuper transitive (_, _, gid) =
  do nodeList <- myGetNodes gid gv
     if transitive
       then updateDaVinciGraph
                 (foldl (getSubSuperClosure (getClassGraph onto) showSuper)
                        empty nodeList) gid gv
       else updateDaVinciGraph
                 (foldl (getSubSuperSingle (getClassGraph onto) showSuper)
                        empty nodeList) gid gv
     A.redisplay gid gv
     return ()

reduceToThisNode :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int) -> IO ()
reduceToThisNode onto gv (name, _, gid) = do
     purgeGraph gid gv
     case gselName name $ getClassGraph onto of
       [] -> return ()
       (_, v, l, _) : _ -> do
           updateDaVinciGraph (([], v, l, []) & empty) gid gv
           A.redisplay gid gv
           return ()

purgeThisNode :: A.GraphInfo -> (String, Int, Int) -> IO ()
purgeThisNode gv (name, _, gid) =
  do (gs, _) <- readIORef gv
     case lookup gid gs of
       Nothing -> return ()
       Just g ->
        do let oldGraph = A.ontoGraph g
               nMap = A.nodeMap g
           (_, mayNodeID) <-
              case findLNode oldGraph name of
                Nothing -> return (oldGraph, Nothing)
                Just nodeID -> return (delNode nodeID oldGraph, Just nodeID)
           case mayNodeID of
             Nothing -> return ()
             Just nodeID ->
               case Map.lookup nodeID nMap of
                 Nothing -> return ()
                 Just node -> do
                     A.delnode gid node gv
                     A.redisplay gid gv
                     return ()

showSuperSubClasses :: MMiSSOntology -> A.GraphInfo -> Bool -> Bool
                    -> (String, Int, Int) -> IO ()
showSuperSubClasses onto gv showSuper transitive (name, _, gid) =
  do if transitive
       then updateDaVinciGraph
              (getSubSuperClosure (getClassGraph onto) showSuper empty name)
              gid gv
       else updateDaVinciGraph (getSubSuperSingle (getClassGraph onto)
                                showSuper empty name) gid gv
     A.redisplay gid gv
     return ()

getSubSuperSingle :: ClassGraph -> Bool -> ClassGraph -> String -> ClassGraph
getSubSuperSingle g showSuper newGr name =
  case findLNode g name of
    Nothing -> g
    Just nodeID ->
      let isaPred (_, _, a) = a == "isa"
          subClassEdges = filter isaPred $ inn g nodeID
          ng = foldl (insPredecessorAndEdge g)
               (insertInitialNode nodeID newGr) subClassEdges
      in if showSuper
           then let superClassEdges = filter isaPred $ out g nodeID
                in foldl (insSuccessorAndEdge g) ng superClassEdges
           else ng
  where
    insertInitialNode :: Node -> ClassGraph -> ClassGraph
    insertInitialNode nodeID gr =
      case match nodeID gr of
        (Nothing, _) -> ([], nodeID, (name, "", OntoClass), []) & gr
        _ -> gr
    insPredecessorAndEdge :: ClassGraph -> ClassGraph -> LEdge String
                          -> ClassGraph
    insPredecessorAndEdge oldGr newGr' (fromNode, toNode, edgeLabel) =
      case fst $ match fromNode oldGr of
        Nothing -> newGr'
        Just (_, _, nodeLabel1, _) ->
           case match fromNode newGr' of
             (Nothing, _) ->
                 ([], fromNode, nodeLabel1, [(edgeLabel, toNode)]) & newGr'
             (Just (p, fromNodeID, nodeLabel2, s), newGr2) ->
                 (p, fromNodeID, nodeLabel2, (edgeLabel, toNode) : s) & newGr2
    insSuccessorAndEdge :: ClassGraph -> ClassGraph -> LEdge String
                        -> ClassGraph
    insSuccessorAndEdge oldGr newGr' (fromNode, toNode, edgeLabel) =
      case fst $ match toNode oldGr of
        Nothing -> newGr'
        Just (_, _, (nodeLabel1, _, _), _) ->
           case match toNode newGr' of
             (Nothing, _) ->
              ([(edgeLabel, fromNode)], toNode, (nodeLabel1, "", OntoClass), [])
              & newGr'
             (Just (p, toNodeID, nodeLabel2, s), newGr2) ->
                 ((edgeLabel, fromNode) : p, toNodeID, nodeLabel2, s) & newGr2

getSubSuperClosure :: ClassGraph -> Bool -> ClassGraph -> String -> ClassGraph
getSubSuperClosure g showSuper newGr name =
  case findLNode g name of
    Nothing -> g
    Just nodeID ->
      let ng = foldl subClassClosure newGr [nodeID]
      in if showSuper
           then foldl (superClassClosure nodeID) ng [nodeID]
           else ng
  where
    superClassClosure :: Node -> ClassGraph -> Node -> ClassGraph
    superClassClosure specialNodeID ng nodeID =
      case fst $ match nodeID g of
        Nothing -> ng
        Just (_, _, (label, _, _), outAdj) ->
          let isaAdj = filter ((== "isa") . fst) outAdj
              ng1 = foldl (superClassClosure specialNodeID) ng
                    $ map snd isaAdj
          in if nodeID == specialNodeID
          then case match specialNodeID ng1 of
     -- This should never be the case, but we somehow have to deal with it
              (Nothing, _) -> (isaAdj, nodeID, (label, "", OntoClass), [])
                              & ng1
              (Just (inAdj, _, _, _), ng2) ->
                  (inAdj, nodeID, (label, "", OntoClass), isaAdj) & ng2
          else case match nodeID ng1 of
              (Nothing, _) -> ([], nodeID, (label, "", OntoClass), isaAdj)
                              & ng1
              (Just (inAdj, _, _, outAdj2), ng2) ->
                  (inAdj ++ isaAdj, nodeID, (label, "", OntoClass), outAdj2)
                  & ng2
{- - subClassClosure hunts transitively all isa-Ajacencies that goes
    into the given node (nodeID).  For all nodes collected, their
    outgoing adjacencies are ignored because we only want to show the
    isa-Relation to the superclass. The given specialNodeID is the ID
    of the node from which the search for subclasses startet. Because
    this node is already in the graph, we have to delete and reinsert
    it with its outgoing adjacencies (which consists of the
    isa-relations to it's superclasses, build by superClassClosure
    beforehand).  - -}
    subClassClosure :: ClassGraph -> Node -> ClassGraph
    subClassClosure ng nodeID =
      case fst $ match nodeID g of
        Nothing -> ng
        Just (inAdj, _, (label, _, _), _) ->
          let isaAdj = filter ((== "isa") . fst) inAdj
              ng1 = foldl subClassClosure ng $ map snd isaAdj
          in case fst $ match nodeID ng1 of
               Nothing -> (isaAdj, nodeID, (label, "", OntoClass), []) & ng1
               _ -> ng1

hideObjectsForVisible :: A.GraphInfo -> (String, Int, Int) -> IO ()
hideObjectsForVisible gv (_, _, gid) =
  do (gs, _) <- readIORef gv
     case lookup gid gs of
       Nothing -> return ()
       Just g ->
         do let oldGraph = A.ontoGraph g
                objectNodeIDs = map ( \ (_, v, _, _) -> v) $
                                gselType (== OntoObject) oldGraph
            purgeGraph gid gv
            updateDaVinciGraph (restrict (`notElem` objectNodeIDs) oldGraph)
                               gid gv
            A.redisplay gid gv
            return ()

createEdgeTypes :: ClassGraph -> [(String, DaVinciArcTypeParms A.EdgeValue)]
createEdgeTypes g = map createEdgeType
   $ nub (map ( \ (_, _, l) -> l) $ labEdges g) ++ ["instanceOf"]
  where
    createEdgeType str =
      case str of
        "isa" ->
             ("isa",
               Thick
               $$$ Head "oarrow"
               $$$ Dir "first"
               $$$ emptyArcTypeParms :: DaVinciArcTypeParms A.EdgeValue)
        "instanceOf" ->
             ("instanceOf",
               Dotted
               $$$ Dir "first"
               $$$ emptyArcTypeParms :: DaVinciArcTypeParms A.EdgeValue)
        _ -> -- "contains"
             (str,
              Solid
              $$$ Head "arrow"
              $$$ ValueTitle (\ (name, _, _) -> return name)
              $$$ emptyArcTypeParms :: DaVinciArcTypeParms A.EdgeValue)

createLocalMenu :: MMiSSOntology -> A.GraphInfo -> LocalMenu (String, Int, Int)
createLocalMenu onto ginfo =
    let relMenus b =
            createRelationMenuButtons b (getRelationNames onto) onto ginfo
        allRels f b = [ Button "All relations" $ f onto ginfo b ["isa"]
                      , Blank ] ++ relMenus b
        superSub' f b1 = Button
            (if b1 then "Sub/Superclasses" else "Subclasses")
            . f onto ginfo b1
        superSub = superSub' showSuperSubClasses
        superSubForVis = superSub' showSuperSubClassesForVisible
        relMen f = Menu (Just "Show relations")
                   [ Menu (Just "Outgoing") $ f False
                   , Menu (Just "Out + In") $ f True ]
        nodeMen f b = Menu (Just $ "Show "
                              ++ if b then "transitively" else "adjacent")
                        . ([ f False b, f True b ] ++)
    in LocalMenu $ Menu Nothing
    [ Menu (Just "For this node")
      [ nodeMen superSub True [relMen $ allRels showAllRelations]
      , nodeMen superSub False
        [relMen $ allRels ( \ o g _ -> showRelationsToNeighbors o g)]
      ]
    , Menu (Just "For visible nodes")
      [ nodeMen superSubForVis True []
      , nodeMen superSubForVis False []
      , Blank
      , Button "Show relations" $ showRelationsForVisible onto ginfo
      , Blank
      , Button "Show objects" $ showObjectsForVisible onto ginfo
      , Button "Hide objects" $ hideObjectsForVisible ginfo
      ]
    , Button "Show whole class graph" $ showWholeClassGraph onto ginfo
    , Button "Show whole object graph" $ showWholeObjectGraph onto ginfo
    , Button "Show relations" $ showRelationDialog ginfo
    , Button "Reduce to this node" $ reduceToThisNode onto ginfo
    , Button "Delete this node" $ purgeThisNode ginfo
    ]

createRelationMenuButtons :: Bool -> [String] -> MMiSSOntology -> A.GraphInfo
                          -> [MenuPrim a ((String, Int, Int) -> IO ())]
createRelationMenuButtons withIncomingRels relNames onto ginfo =
    map createButton relNames
  where
    createButton name = Button name
        $ showAllRelations onto ginfo withIncomingRels
              $ delete name $ relNames ++ ["isa"]

myDeleteNode :: A.Descr -> A.GraphInfo -> A.Result
             -> (Int, (String, DaVinciNode (String, Int, Int)))
             -> IO A.Result
myDeleteNode gid gv _ node = A.delnode gid (fst node) gv

purgeGraph :: Int -> A.GraphInfo -> IO A.Result
purgeGraph gid gv =
  do (gs, _) <- readIORef gv
     case lookup gid gs of
       Just g -> do
         A.writeOntoGraph gid empty gv
         A.writeNodeMap gid Map.empty gv
         foldM (myDeleteNode gid gv) (A.Result 0 Nothing)
               $ Map.toList $ A.nodes g
       Nothing -> return $ A.Result 0 $ Just $
                  "Graph id " ++ show gid ++ " not found"

myGetNodes :: Int -> A.GraphInfo -> IO [String]
myGetNodes gid gv =
  do (gs, _) <- readIORef gv
     case lookup gid gs of
       Just g -> return $ map ( \ (_, (name, _, _)) -> name)
                 $ labNodes $ A.ontoGraph g
       Nothing -> return []


getPureClassGraph :: ClassGraph -> ClassGraph
getPureClassGraph g =
    let classNodeList = map fst
          $ getTypedNodes [OntoClass, OntoPredicate] g
    in restrict (`elem` classNodeList) g


restrict :: DynGraph gr => (Node -> Bool) -> gr a b -> gr a b
restrict f = ufold cfilter empty
            where cfilter (p, v, l, s) g =
                      if f v then (p', v, l, s') & g else g
                   where p' = filter (f . snd) p
                         s' = filter (f . snd) s


getTypedNodes :: [OntoObjectType] -> ClassGraph
              -> [LNode (String, String, OntoObjectType)]
getTypedNodes ts = map labNode' . gselType (`elem` ts)

showRelationDialog :: A.GraphInfo -> (String, Int, Int) -> IO ()
showRelationDialog gv (_ , _, gid) =
  do (gs, _) <- readIORef gv
     case lookup gid gs of
       Nothing -> return ()
       Just g ->
         do let rvs = A.relViewSpecs g
                specEntries = S.row $ map relSpecToFormEntry rvs
                form = firstRow S.// specEntries
            S.doForm "Show relations" form
            return ()
  where
    firstRow = S.newFormEntry "" () S.\\ S.newFormEntry "Show" ()
       S.\\ S.newFormEntry "Transitive" ()
    relSpecToFormEntry (A.RelViewSpec relname b1 b2) =
      S.newFormEntry relname () S.\\ S.newFormEntry "" b1
       S.\\ S.newFormEntry "" b2
