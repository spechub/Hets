{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(uni)

displays an ontology graph
-}

module Taxonomy.MMiSSOntologyGraph (displayClassGraph) where

import Data.List
import Control.Monad
import Data.IORef
import Data.Char

import DaVinciGraph
import GraphDisp
import GraphConfigure
import qualified HTk as H
import qualified SimpleForm as S
import Taxonomy.MMiSSOntology

import qualified Common.Lib.Map as Map
import Common.Lib.Graph
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Query.TransClos
import Data.Graph.Inductive.Query.DFS

import qualified Taxonomy.AbstractGraphView as A

displayClassGraph :: MMiSSOntology -> Maybe String -> IO ()
displayClassGraph onto startClass =
  do main <- H.initHTk []
     ginfo <- A.initgraphs
--     emptyRelViewSpec <- return(map (\(relname) -> RelViewSpec relname False False)
--                                    (getRelations onto))
     classGraph <- case startClass of
                     Nothing -> return (getPureClassGraph (getClassGraph onto))
                     Just(className) -> case (gsel (\(p,v,(l,_,_),s) -> l == className) (getClassGraph onto)) of
                                          [] -> return (getPureClassGraph (getClassGraph onto))
                                          ((p,v,l,s):_) -> return(([],v,l,[]) & empty)
     A.Result gid err <-
       A.makegraph  (getOntologyName onto)
           [GlobalMenu (Button "Knopf2" (putStrLn "Knopf2 wurde gedrückt"))]
           [("class", Box $$$ Color "#e0eeee" $$$
                   createLocalMenu onto ginfo main
                   $$$ ValueTitle ( \ (name,descr,gid) -> return name) $$$
                   emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)
            ),
            ("predicate", Box $$$ Color "#ffd300" $$$
                   createLocalMenu onto ginfo main
                   $$$ ValueTitle ( \ (name,descr,gid) -> return name) $$$
                   emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)
            ),
            ("object", Box  $$$ Color "#ffffA0" $$$
                   createLocalMenu onto ginfo main
                   $$$ ValueTitle ( \ (name,descr,gid) -> return name) $$$
                   emptyNodeTypeParms :: DaVinciNodeTypeParms (String,Int,Int)
            )]
           (createEdgeTypes (getClassGraph onto))
           []
           ginfo
     updateDaVinciGraph classGraph gid ginfo
     setEmptyRelationSpecs gid ginfo onto
     A.Result gid _ <- A.redisplay gid ginfo
     return()
--     A.Result eid err2 <- addlink gid "relation" "RelationTitle" nid1 nid2 ginfo
--     putStr (show ontology)
--     getLine
--     delgraph gid ginfo

{--
emptyNodeMap :: A.NodeMapping
emptyNodeMap = Map.empty
--}

setEmptyRelationSpecs :: A.Descr -> A.GraphInfo -> MMiSSOntology -> IO ()
setEmptyRelationSpecs gid gv onto =
  do (gs,_) <- readIORef gv
     case lookup gid gs of
       Nothing -> return()
       Just g ->
         do A.Result gid err <- A.writeRelViewSpecs gid emptyRelViewSpecs gv
            return()
  where
    emptyRelViewSpecs = map (\(relname) -> (A.RelViewSpec relname False False))
                            (getRelationNames onto)


{--
createDaVinciGraph :: A.NodeMapping -> Gr (String, String, OntoObjectType) String
                        -> String -> A.Descr -> A.GraphInfo -> IO (A.NodeMapping)

createDaVinciGraph nodeMap classGraph nodeType gid ginfo =
  do nodeMap1 <- foldM (createNode gid ginfo) nodeMap (labNodes classGraph)
     nodeMap2 <- foldM (createLink gid ginfo) nodeMap1 (labEdges classGraph)
--     A.Result _ _ <- A.writeOntoGraph gid classGraph ginfo
     return nodeMap2
  where
    createNode :: Int -> A.GraphInfo -> A.NodeMapping -> LNode (String, String, OntoObjectType) -> IO (A.NodeMapping)
    createNode gid ginfo nMap (nodeID, (label, _, _)) =
      do (A.Result nid _) <- A.addnode gid nodeType label ginfo
         return (Map.insert nodeID nid nMap)

    createLink :: A.Descr -> A.GraphInfo -> A.NodeMapping -> LEdge String -> IO (A.NodeMapping)
    createLink gid ginfo nMap (node1, node2, edgeLabel) =
      do dNodeID_1 <- case Map.lookup node1 nMap of
                        Nothing -> return (-1)
                        Just(n) -> return(n)
         dNodeID_2 <- case Map.lookup node2 nMap of
                        Nothing -> return (-1)
                        Just(n) -> return(n)
         if ((dNodeID_1 == -1) || (dNodeID_2 == -1))
           then return nMap
           else do A.Result eid _ <- if (edgeLabel == "isa")
                                       then A.addlink gid edgeLabel edgeLabel dNodeID_2 dNodeID_1 ginfo
                                       else A.addlink gid edgeLabel edgeLabel dNodeID_1 dNodeID_2 ginfo
                   return nMap
--}


-- Klassengraph -> Objekte dazu (mit Links auf Klasse)
--

-- Klassengraph vorhanden -> Objektgraph als Input -> Objekte und Links sowie 'instanceOf' einfügen
-- Klassen vorhanden -> Objekte hinzu:

updateDaVinciGraph :: Gr (String,String,OntoObjectType) String ->
                              A.Descr -> A.GraphInfo -> IO ()

updateDaVinciGraph newGraph gid gv =
  do (gs,_) <- readIORef gv
     case lookup gid gs of
       Nothing -> return()
       Just g ->
        do oldGraph <- return(A.ontoGraph g)
           nMap <- return(A.nodeMap g)
           nodeMap1 <- foldM (createNode gid gv oldGraph) nMap (labNodes newGraph)
           nodeMap2 <- foldM (createLink gid gv) nodeMap1 (labEdges newGraph)
           A.Result gid err <- A.writeOntoGraph gid newGraph gv
           A.Result gid err2 <- A.writeNodeMap gid nodeMap2 gv
           case err of
             Nothing -> return()
             Just(str) -> putStr str
           return()
        where
          getTypeLabel OntoClass = "class"
          getTypeLabel OntoObject = "object"
          getTypeLabel OntoPredicate = "predicate"
          createNode :: Int -> A.GraphInfo -> Gr (String,String,OntoObjectType) String ->
                          A.NodeMapping -> LNode (String, String, OntoObjectType) -> IO (A.NodeMapping)
          createNode gid ginfo oldGraph nMap (nodeID, (name, className, objectType)) =
            case Map.lookup nodeID nMap of
              Just(_) -> return nMap
              Nothing ->
                do (A.Result nid err) <- A.addnode gid (getTypeLabel objectType) name ginfo
                   case err of
                     Nothing -> return (Map.insert nodeID nid nMap)
                     Just(str) -> do putStr str
                                     return (Map.insert nodeID nid nMap)

          createLink :: A.Descr -> A.GraphInfo -> A.NodeMapping -> LEdge String -> IO (A.NodeMapping)
          createLink gid ginfo nMap (node1, node2, edgeLabel) =
            do dNodeID_1 <- case Map.lookup node1 nMap of
                              Nothing -> return (-1)
                              Just(n) -> return(n)
               dNodeID_2 <- case Map.lookup node2 nMap of
                              Nothing -> return (-1)
                              Just(n) -> return(n)
               if ((dNodeID_1 == -1) || (dNodeID_2 == -1))
                 then return nMap
                 else do A.Result eid err <-
                            if (edgeLabel == "isa") || (edgeLabel == "instanceOf") || (edgeLabel == "livesIn") || (edgeLabel == "proves")
                              then A.addlink gid edgeLabel edgeLabel dNodeID_2 dNodeID_1 ginfo
--                            else A.addlink gid edgeLabel edgeLabel dNodeID_2 dNodeID_1 ginfo
                              else A.addlink gid edgeLabel edgeLabel dNodeID_1 dNodeID_2 ginfo
                         case err of
                           Nothing -> return()
                           Just(str) -> putStr str
                         return nMap


showRelationsForVisible :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int) -> IO ()
showRelationsForVisible onto gv (name,descr,gid) =
  do (gs,_) <- readIORef gv
     case lookup gid gs of
       Nothing -> return()
       Just g ->
         do oldGraph <- return(A.ontoGraph g)
            let nodesInOldGraph = map (\(nodeID,(_,_,_)) -> nodeID) (labNodes oldGraph)
                newGr = nfilter (`elem` nodesInOldGraph) (getClassGraph onto)
            (A.Result descr error) <- purgeGraph gid gv
            updateDaVinciGraph newGr gid gv
            A.redisplay gid gv
            return ()



showObjectsForVisible :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int) -> IO ()
showObjectsForVisible onto gv (name,descr,gid) =
  do (gs,_) <- readIORef gv
     case lookup gid gs of
       Nothing -> return()
       Just g ->
         do oldGraph <- return(A.ontoGraph g)
            let classesInOldGraph = map (\(_,_,(className,_,_),_) -> className)
                                        (filter (\(_,_,(_,_,objectType),_) -> objectType == OntoClass)
                                             (map (context oldGraph) (nodes oldGraph)))
                objectList = map (\(nid,_) -> nid)
                                 (filter (findObjectsOfClass classesInOldGraph)
                                            (getTypedNodes (getClassGraph onto) [OntoObject]))
                objectGr = nfilter (`elem` objectList) (getClassGraph onto)
            updateDaVinciGraph (makeObjectGraph oldGraph (getPureClassGraph (getClassGraph onto)) objectGr) gid gv
            A.redisplay gid gv
            return ()
  where
    findObjectsOfClass classList (_,(_,className,_)) = className `elem` classList


showWholeObjectGraph :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int) -> IO ()
showWholeObjectGraph onto gv (name,descr,gid) =
  do oldGv <- readIORef gv
     (A.Result descr error) <- purgeGraph gid gv
     let objectList = map (\(nid,_) -> nid) (getTypedNodes (getClassGraph onto) [OntoObject])
         objectGraph = nfilter (`elem` objectList) (getClassGraph onto)
     updateDaVinciGraph (makeObjectGraph empty (getClassGraph onto) objectGraph) gid gv
     case error of
       Just _ -> do writeIORef gv oldGv
                    return ()
       Nothing -> do A.redisplay gid gv
                     return ()



{-- makeObjectGraph bekommt den alten Graphen, in den die Objekte und deren Klassen einzubeziehen sind, den Klassen-Graphen, in dem alle Klassen vorhanden sein sollten, sowie den Graphen mit den einzufügenden Objekten und deren Links übergeben. Die Funktion geht den Objektgraphen durch, fügt die Objekt-Knoten in den alten Graphen ein.
Für jeden eingefügten Objekt-Knoten sucht die Funktion im Klassengraphen dessen Klasse und fügt diese als Klassen-Knoten ebenfalls in den alten Graphen ein. Zwischen Klasse und Objekt wird eine InstanceOf-Kante eingefügt. Bei allen Einfüge-Operationen wird vorher geprüft, ob der Knoten schon drin war oder nicht.
--}

makeObjectGraph :: Gr (String,String,OntoObjectType) String
                   -> Gr (String,String,OntoObjectType) String -> Gr (String,String,OntoObjectType) String
                        -> Gr (String,String,OntoObjectType) String

makeObjectGraph oldGr classGr objectGr =
  let newGr = insNodes (labNodes objectGr) oldGr
      newGr2 = foldl insEdgeSecurely newGr (labEdges objectGr)
      newGr3 = foldl (insInstanceOfEdge classGr) newGr2 (labNodes objectGr)
  in newGr3
  where
    insEdgeSecurely gr (node1,node2,label) =
      case match node1 gr of
        (Nothing,_) -> gr
        (Just(_),_) ->
          case match node2 gr of
            (Nothing,_) -> gr
            (Just(_),_) -> insEdge (node1,node2,label) gr

    insInstanceOfEdge classGr gr (_,(objectName, className,_)) =
      case findLNode gr className of
        Nothing -> case findLNode classGr className of
                     Nothing -> gr
                     Just(classNodeID) -> insInstanceOfEdge1 (insNode (classNodeID,(className, "", OntoClass)) gr)
                                            classNodeID objectName
        Just(classNodeID) -> insInstanceOfEdge1 gr classNodeID objectName

    insInstanceOfEdge1 gr classNodeID objectName =
      case findLNode gr objectName of
        Nothing -> gr
        Just(objectNodeID) -> insEdge (objectNodeID, classNodeID, "instanceOf") gr


showWholeClassGraph :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int) -> IO ()
showWholeClassGraph onto gv (name, descr, gid) =
  do oldGv <- readIORef gv
     (A.Result descr error) <- purgeGraph gid gv
     updateDaVinciGraph (getPureClassGraph (getClassGraph onto)) gid gv
     case error of
       Just _ -> do writeIORef gv oldGv
                    return ()
       Nothing -> do A.redisplay gid gv
                     return ()

showRelationsToNeighbors :: MMiSSOntology -> A.GraphInfo -> Bool -> [String] -> (String, Int, Int) -> IO ()
showRelationsToNeighbors onto gv withIncoming rels (name, _, gid) =
  do oldGv <- readIORef gv
--     (A.Result descr error) <- purgeGraph gid gv
     updateDaVinciGraph (reduceToNeighbors (getClassGraph onto) withIncoming name rels) gid gv
     writeIORef gv oldGv
     return ()
--     case error of
--       Just _ -> do writeIORef gv oldGv
--                  return ()
--       Nothing -> do A.redisplay gid gv
--                   return ()


reduceToNeighbors :: Gr (String,String,OntoObjectType) String -> Bool -> String -> [String]
                     -> Gr (String,String,OntoObjectType) String
reduceToNeighbors g withIncoming name forbiddenRels =
  case findLNode g name of
    Nothing -> g
    Just(node) ->
      let (p,v,l,s) = context g node
          p' = filter (\(edgeLabel,_) -> mynotElem forbiddenRels edgeLabel) p
          s' = filter (\(edgeLabel,_) -> mynotElem forbiddenRels edgeLabel) s
          nodes = (map (\(l,v') -> v') p') ++ (map (\(l1,v1') -> v1') s')
          newGr = foldl (myInsNode g) empty nodes
      in (p',v,l,s') & newGr
  where
    mynotElem l a = notElem a l
    myInsNode gr newGr nodeID =
      case match nodeID newGr of
        (Nothing,_) -> ([],nodeID, lab' (context gr nodeID),[]) & newGr
        (Just(_),_) -> newGr


showAllRelations :: MMiSSOntology -> A.GraphInfo -> Bool -> [String] -> (String, Int, Int) -> IO ()
showAllRelations onto gv withIncoming rels (name, _, gid) =
  do oldGv <- readIORef gv
--     (A.Result descr error) <- purgeGraph gid gv
     newGr <- return(reduceToRelations (getClassGraph onto) empty withIncoming rels name)
     updateDaVinciGraph newGr gid gv
     writeIORef gv oldGv
     return ()
--     case error of
--       Just _ -> do writeIORef gv oldGv
--                  return ()
--      Nothing -> do A.redisplay gid gv
--                   return ()


{--
reduceToRelations bekommt den aktuellen Graph, einen Klassenknoten darin sowie eine Liste mit Relationsnamen,
die _nicht_ angezeigt werden sollen, übergeben. Ausgehend von dem Klassenknoten werden aus dem Ontologiegraphen
transitiv alle Klassenknoten ermittelt, die über eine der nicht-ausgeblendeten Relationen erreicht werden
können. Diese werden (mit ihren Relationen zu ebenfalls neu hinzugefügten Knoten) in den aktuellen Graphen
eingefügt. Bezüge zwischen neu eingefügten Knoten uns alten????
Im ersten Schritt werden transitiv alle Knoten ermittelt, die mit dem ausgewählten Knoten in einer der
nicht verbotenen Beziehungen stehen. Dann wird rekursiv für jeden dieser gefunden Knoten dessen direkte
Subklassen ermittelt und für diese wiederum die direkten Nachbarn ermittelt und aufgenommen.

g1 = Gesamter Ontologiegraph nach erlaubten Relationen gefiltert
nodeList = Alle Knoten der transitiven Hülle des ausgewählten Knotens (selectedNode)
(delNodes toDelete g1) = Ontologiegraph reduziert auf die Knoten (und Kanten) der transitiven Hülle
g2 = Merge aus dem aktuellen Graphen g und der transitiven Hülle von selectedNode
newNodesList = Zu g neu hinzugekommene Knoten.
--}

reduceToRelations :: Gr (String,String,OntoObjectType) String -> Gr (String,String,OntoObjectType) String
                     -> Bool -> [String] -> String
                     -> Gr (String,String,OntoObjectType) String
reduceToRelations wholeGraph g withIncoming forbiddenRels name =
  let g1 = elfilter (mynotElem forbiddenRels) wholeGraph
  in case findLNode g1 name of
       Nothing -> g
       Just(selectedNode) ->
          let nodeList = if (withIncoming == True)
                           then udfs [selectedNode] g1
                           else dfs [selectedNode] g1
              toDelete = ((nodes g1) \\ nodeList)
              g1' = (delNodes toDelete g1)
              g2 =  mergeGraphs g1' g
              newNodesList = (nodeList \\ (nodes g))
          in if (newNodesList == [])
               then g2
               else foldl (followRelationOverSubClasses wholeGraph withIncoming forbiddenRels) g2 newNodesList
  where
    mynotElem l a = notElem a l


followRelationOverSubClasses :: Gr (String,String,OntoObjectType) String -> Bool -> [String] ->
   Gr (String,String,OntoObjectType) String -> Node -> Gr (String,String,OntoObjectType) String
followRelationOverSubClasses wholeGraph withIncoming forbiddenRels g selectedNode =
 let g1 = elfilter (== "isa") wholeGraph
 in case match selectedNode g1 of
      (Nothing,_) -> g
      (Just(_),_) ->
         let subclasses = rdfs [selectedNode] g1
             newNodes = subclasses \\ (nodes g)
         in if (newNodes == [])
              then g
              else
                let
                  toDelete = (nodes g1) \\ subclasses
                  g2 = mergeGraphs (delNodes toDelete g1) g
                in  foldl (transClosureForNode wholeGraph withIncoming forbiddenRels) g2 newNodes
 where
   transClosureForNode wGraph withIncoming forbiddenRels g node =
     let (name,_,_) = lab' (context wGraph node)
     in reduceToRelations wholeGraph g withIncoming forbiddenRels name

{--
    insEdgeSecurely gr (node1,node2,label) =
      case match node1 gr of
        (Nothing,_) ->
        (Just(_),_) ->
          case match node2 gr of
            (Nothing,_) -> gr
            (Just(_),_) -> insEdge (node1,node2,label) gr

    insNodeSecurely gr (node, label) =
       case match node gr of
         (Nothing,_) -> insNode (node,label) gr
         (Just(_),_) -> gr
--}

mergeGraphs :: Gr (String,String,OntoObjectType) String -> Gr (String,String,OntoObjectType) String -> Gr (String,String,OntoObjectType) String

mergeGraphs g1 g2 =
  insEdges (labEdges g2) (insNodes ((labNodes g2) \\ (labNodes g1)) g1)


showSuperSubClassesForVisible :: MMiSSOntology -> A.GraphInfo -> Bool -> Bool -> (String, Int, Int) -> IO ()
showSuperSubClassesForVisible onto gv showSuper transitive (name, descr, gid) =
  do nodeList <- myGetNodes gid gv
     if transitive
       then updateDaVinciGraph
                 (foldl (getSubSuperClosure (getClassGraph onto) showSuper) empty nodeList)
                 gid gv
       else updateDaVinciGraph
                 (foldl (getSubSuperSingle (getClassGraph onto) showSuper) empty nodeList)
                 gid gv
     A.redisplay gid gv
     return ()


reduceToThisNode :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int) -> IO ()
reduceToThisNode onto gv (name, descr, gid) =
  do oldGv <- readIORef gv
     A.Result _ _ <- purgeGraph gid gv
     case (gsel (\(p,v,(l,_,_),s) -> l == name) (getClassGraph onto)) of
       [] -> return()
       ((p,v,l,s):_) -> do
                           updateDaVinciGraph (([],v,l,[]) & empty) gid gv
                           A.redisplay gid gv
                           return()


purgeThisNode :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int) -> IO ()
purgeThisNode onto gv (name, descr, gid) =
  do (gs,_) <- readIORef gv
     case lookup gid gs of
       Nothing -> return()
       Just g ->
        do oldGraph <- return(A.ontoGraph g)
           nMap <- return(A.nodeMap g)
           (newGraph,mayNodeID) <-
              case findLNode oldGraph name of
                Nothing -> return(oldGraph, Nothing)
                Just(nodeID) -> return((delNode nodeID oldGraph), Just(nodeID))
           case mayNodeID of
             Nothing -> return()
             Just(nodeID) ->
               case Map.lookup nodeID nMap of
                 Nothing -> return()
                 Just(node) -> do A.delnode gid node gv
                                  A.redisplay gid gv
                                  return()


showSuperSubClasses :: MMiSSOntology -> A.GraphInfo -> Bool -> Bool -> (String, Int, Int) -> IO ()
showSuperSubClasses onto gv showSuper transitive (name, descr, gid) =
  do oldGv <- readIORef gv
     if transitive
       then updateDaVinciGraph
              (getSubSuperClosure (getClassGraph onto) showSuper empty name) gid gv
       else updateDaVinciGraph (getSubSuperSingle (getClassGraph onto) showSuper empty name) gid gv
     A.redisplay gid gv
     return ()


getSubSuperSingle :: Gr (String,String,OntoObjectType) String -> Bool -> Gr (String,String,OntoObjectType) String
                        -> String -> Gr (String,String,OntoObjectType) String
getSubSuperSingle g showSuper newGr name =
  case findLNode g name of
    Nothing -> g
    Just(nodeID) ->
      let subClassEdges = filter ((== "isa"). (\(_,_,a) -> a)) (inn g nodeID)
          ng = foldl (insPredecessorAndEdge g) (insertInitialNode nodeID name newGr) subClassEdges
      in if showSuper
           then let superClassEdges = filter ((== "isa").(\(_,_,a) -> a)) (out g nodeID)
                in foldl (insSuccessorAndEdge g) ng superClassEdges
           else ng
  where
    insertInitialNode :: Node -> String ->  Gr (String,String,OntoObjectType) String
                          ->  Gr (String,String,OntoObjectType) String
    insertInitialNode nodeID name gr =
      case match nodeID gr of
        (Nothing,_) -> ([], nodeID, (name,"",OntoClass),[]) & gr
        otherwise -> gr

    insPredecessorAndEdge :: Gr (String,String,OntoObjectType) String -> Gr (String,String,OntoObjectType) String
                               -> LEdge String -> Gr (String,String,OntoObjectType) String
    insPredecessorAndEdge oldGr newGr (fromNode, toNode, edgeLabel) =
      case match fromNode oldGr of
        (Nothing, _) -> newGr
        (Just ((_,_,nodeLabel,_)),_) ->
           case match fromNode newGr of
             (Nothing, _) -> ([], fromNode, nodeLabel, [(edgeLabel, toNode)]) & newGr
             (Just((p,fromNodeID,nodeLabel,s)), newGr2) -> (p,fromNodeID,nodeLabel, ((edgeLabel,toNode):s)) & newGr2

    insSuccessorAndEdge :: Gr (String,String,OntoObjectType) String -> Gr (String,String,OntoObjectType) String
                            -> LEdge String -> Gr (String,String,OntoObjectType) String
    insSuccessorAndEdge oldGr newGr (fromNode, toNode, edgeLabel) =
      case match toNode oldGr of
        (Nothing, _) -> newGr
        (Just ((_,_,(nodeLabel,_,_),_)),_) ->
           case match toNode newGr of
             (Nothing,_) -> ([(edgeLabel, fromNode)], toNode, (nodeLabel,"",OntoClass), []) & newGr
             (Just((p, toNodeID, nodeLabel, s)), newGr2) -> (((edgeLabel, fromNode):p), toNodeID, nodeLabel, s) & newGr2


getSubSuperClosure :: Gr (String,String,OntoObjectType) String -> Bool
                        -> Gr (String,String,OntoObjectType) String -> String
                        -> Gr (String,String,OntoObjectType) String
getSubSuperClosure g showSuper newGr name =
  case findLNode g name of
    Nothing -> g
    Just(nodeID) ->
      let ng = foldl (subClassClosure g) newGr [nodeID]
      in if showSuper
           then foldl (superClassClosure g nodeID) ng [nodeID]
           else ng
  where
    superClassClosure :: Gr (String,String,OntoObjectType) String -> Node
                         -> Gr (String,String,OntoObjectType) String -> Node
                         -> Gr (String,String,OntoObjectType) String
    superClassClosure g specialNodeID ng nodeID =
      case match nodeID g of
        (Nothing, _) -> ng
        (Just((_,_,(label,_,_),outAdj)), _) ->
          let isaAdj = filter ((== "isa") . fst) outAdj
              ng1 = foldl (superClassClosure g specialNodeID) ng (map snd isaAdj)
          in if (nodeID == specialNodeID)
               then case match specialNodeID ng1 of
                      -- This should never be the case, but we somehow have to deal with it
                      (Nothing, _) -> (isaAdj, nodeID, (label,"",OntoClass), []) & ng1
                      (Just((inAdj,_,_,_)), ng2) -> (inAdj, nodeID, (label, "",OntoClass), isaAdj) & ng2
               else case match nodeID ng1 of
                      (Nothing, _) -> ([], nodeID, (label,"",OntoClass), isaAdj) & ng1
                      (Just((inAdj,_,_,outAdj)), ng2) -> (inAdj ++ isaAdj,nodeID,(label,"",OntoClass),outAdj) & ng2

{-- subClassClosure hunts transitively all isa-Ajacencies that goes into the given node (nodeID).
    For all nodes collected, their outgoing adjacencies are ignored because we only want to
    show the isa-Relation to the superclass. The given specialNodeID is the ID of the node from
    which the search for subclasses startet. Because this node is already in the graph, we
    have to delete and reinsert it with its outgoing adjacencies (which consists of the
    isa-relations to it's superclasses, build by superClassClosure beforehand).
--}
    subClassClosure ::  Gr (String,String,OntoObjectType) String ->  Gr (String,String,OntoObjectType) String
                         -> Node -> Gr (String,String,OntoObjectType) String
    subClassClosure g ng nodeID =
      case match nodeID g of
        (Nothing, _) -> ng
        (Just((inAdj,_,(label,_,_), outAdj)), _) ->
          let isaAdj = filter ((== "isa") . fst) inAdj
              ng1 = foldl (subClassClosure g) ng (map snd isaAdj)
          in case match nodeID ng1 of
               (Nothing, _) -> (isaAdj, nodeID, (label,"",OntoClass), []) & ng1
               (Just(_),_) -> ng1



hideObjectsForVisible :: MMiSSOntology -> A.GraphInfo -> (String, Int, Int) -> IO ()
hideObjectsForVisible onto gv (name,descr,gid) =
  do (gs,_) <- readIORef gv
     case lookup gid gs of
       Nothing -> return()
       Just g ->
         do oldGraph <- return(A.ontoGraph g)
            let objectNodeIDs = map (\(_,v,_,_) -> v) (gsel (\(_,_,(_,_,t),_) -> t == OntoObject) oldGraph)
            A.Result _ _ <- purgeGraph gid gv
            updateDaVinciGraph (nfilter (`notElem` objectNodeIDs) oldGraph) gid gv
            A.redisplay gid gv
            return ()



createEdgeTypes ::  Gr (String,String,OntoObjectType) String -> [(String,DaVinciArcTypeParms (String,A.Descr))]
createEdgeTypes g = map createEdgeType ((nub (map (\(_,_,l) -> l) (labEdges g))) ++ ["instanceOf"])
  where
    createEdgeType str =
      case str of
        "isa" ->
             ("isa",
               Thick
               $$$ Head "oarrow"
               $$$ Dir "first"
               $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int))
        "instanceOf" ->
             ("instanceOf",
               Dotted
               $$$ Dir "first"
               $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int))
        "contains" ->
             (str,
              Solid
              $$$ Head "arrow"
              $$$ ValueTitle (\ (name, _) -> return name)
              $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int))
        otherwise ->
             (str,
              Solid
              $$$ Head "arrow"
--              $$$ Dir "first"
              $$$ ValueTitle (\ (name, _) -> return name)
--               $$$ TitleFunc (\ (name, _) -> name)
              $$$ emptyArcTypeParms :: DaVinciArcTypeParms (String,Int))


createLocalMenu onto ginfo mainWindow =
                   LocalMenu (Menu Nothing
                    ([(Menu (Just "For this node")
                        [  (Menu (Just "Show transitively")
                             [Button "Subclasses" (showSuperSubClasses onto ginfo False True),
                              Button "Sub/Superclasses" (showSuperSubClasses onto ginfo True True),
                              (Menu (Just "Show relations")
                                [(Menu (Just "Outgoing")
                                  ([Button "All relations" (showAllRelations onto ginfo False ["isa"]),
                                   Blank] ++ (createRelationMenuButtons False (getRelationNames onto) onto ginfo)))
                                ,(Menu (Just "Out + In")
                                 ([Button "All relations" (showAllRelations onto ginfo True ["isa"]),
                                  Blank] ++ (createRelationMenuButtons True (getRelationNames onto) onto ginfo)))
                             ])
                           ])
                          ,(Menu (Just "Show adjacent")
                             [Button "Subclasses" (showSuperSubClasses onto ginfo False False),
                              Button "Sub/Superclasses" (showSuperSubClasses onto ginfo True False),
                              (Menu (Just "Show relations")
                                 [(Menu (Just "Outgoing")
                                     ([Button "All relations" (showRelationsToNeighbors onto ginfo False ["isa"]),
                                       Blank] ++ (createRelationMenuButtons False (getRelationNames onto) onto ginfo)))
                                 ,(Menu (Just "Out + In")
                                    ([Button "All relations" (showRelationsToNeighbors onto ginfo True ["isa"]),
                                     Blank] ++ (createRelationMenuButtons True (getRelationNames onto) onto ginfo)))
                             ])])
                        ]
                      ),
                      (Menu (Just "For visible nodes")
                        [  (Menu (Just "Show transitively")
                             [Button "Subclasses" (showSuperSubClassesForVisible onto ginfo False True),
                              Button "Sub/Superclasses" (showSuperSubClassesForVisible onto ginfo True True)])
                          ,(Menu (Just "Show adjacent")
                             [Button "Subclasses" (showSuperSubClassesForVisible onto ginfo False False),
                              Button "Sub/Superclasses" (showSuperSubClassesForVisible onto ginfo True False)])
                          ,Blank
                          ,Button "Show relations" (showRelationsForVisible onto ginfo)
                          ,Blank
                          ,Button "Show objects" (showObjectsForVisible onto ginfo)
                          ,Button "Hide objects" (hideObjectsForVisible onto ginfo)
                        ]
                      ),
                      Button "Show whole class graph" (showWholeClassGraph onto ginfo),
                      Button "Show whole object graph" (showWholeObjectGraph onto ginfo),
                      Button "Show relations" (showRelationDialog mainWindow onto ginfo),
                      Button "Reduce to this node" (reduceToThisNode onto ginfo),
                      Button "Delete this node" (purgeThisNode onto ginfo)
                      ]
                     ))


createRelationMenuButtons withIncomingRels relNames onto ginfo = map createButton relNames
  where
    createButton name = (Button (name)
                                (showAllRelations onto ginfo withIncomingRels (delete name (relNames ++ ["isa"]))))


findLNode :: Gr (String,String,OntoObjectType) String -> String -> Maybe Node

findLNode gr label = case (gsel (\(p,v,(l,_,_),s) -> l == label) gr) of
                      [] -> Nothing
                      conList -> Just(node' (head conList))

myDeleteNode :: A.Descr -> A.GraphInfo -> A.Result -> (Int,(String,DaVinciNode (String,Int,Int))) -> IO (A.Result)
myDeleteNode gid gv _ node = A.delnode gid (fst node) gv


purgeGraph :: Int -> A.GraphInfo -> IO (A.Result)
purgeGraph gid gv =
  do (gs,ev_cnt) <- readIORef gv
     case lookup gid gs of
       Just g -> do A.Result _ _ <- A.writeOntoGraph gid empty gv
                    A.Result _ _ <- A.writeNodeMap gid Map.empty gv
                    foldM (myDeleteNode gid gv) (A.Result 0 Nothing) (A.nodes g)
       Nothing -> return (A.Result 0 (Just ("Graph id "++show gid++" not found")))


myGetNodes :: Int -> A.GraphInfo -> IO ([String])
myGetNodes gid gv =
  do (gs,ev_cnt) <- readIORef gv
     case lookup gid gs of
       Just g -> return(map (\(_,(name,_,_)) -> name) (labNodes (A.ontoGraph g)))
--       Just g -> return (map (\(_,(name,_)) -> name) (A.nodes g))
       Nothing -> return([])


getPureClassGraph :: Gr (String,String,OntoObjectType) String
                  -> Gr (String,String,OntoObjectType) String
-- getPureClassGraph g = efilter (\(_,_,edgeType) -> edgeType == "isa") g
getPureClassGraph g =
    let classNodeList = map (\(nid,_) -> nid)
                            (getTypedNodes g [OntoClass,OntoPredicate])
    in nfilter (`elem` classNodeList) g


nfilter :: DynGraph gr => (Node -> Bool) -> gr a b -> gr a b
nfilter f = ufold cfilter empty
            where cfilter (p,v,l,s) g = if (f v)
                                          then (p',v,l,s') & g
                                          else g
                   where p' = filter (\(b,u)->f u) p
                         s' = filter (\(b,w)->f w) s


getTypedNodes :: Gr (String,String,OntoObjectType) String
              -> [OntoObjectType]
              -> [LNode (String, String, OntoObjectType)]
getTypedNodes g ts =
  map labNode' (gsel (\(_,_,(_,_,objType),_) -> objType `elem` ts) g)

{--
createRelationDialog :: H.HTk -> [A.RelationViewSpec] -> IO()
createRelationDialog parentContainer rvs =
  do relations <- map
     w <- H.createToplevel [H.width 500,
                            H.height ((genericLength relations) * 23)]
     txt1 <- H.newLabel w [H.text "Show"]
     H.grid txt1 [H.GridPos (1,0), H.Sticky H.E]
     txt2 <- H.newLabel w [H.text "Transitive"]
     H.grid txt2 [H.GridPos (2,0), H.Sticky H.E]
     foldM (myNewRelationEntry w) 1 relations
--     click <- H.clicked (fst (head realtionEntries))
--     H.spawnEvent
--      (H.forever
--        (click H.>>> do b H.# H.text "Test"))
     return()
  where
    myNewRelationEntry w lineNr relname =
      do lab <- H.newLabel w [H.text (relname)]
         H.grid lab [H.GridPos (0,lineNr), H.Sticky H.W]
         cb1 <- H.newCheckButton w []
         H.grid cb1 [H.GridPos (1,lineNr), H.Sticky H.E]
         cb2 <- H.newCheckButton w []
         H.grid cb2 [H.GridPos (2,lineNr), H.Sticky H.E]
         return(lineNr + 1)
--}

showRelationDialog :: H.HTk -> MMiSSOntology -> A.GraphInfo -> (String, Int, Int) -> IO ()
showRelationDialog parentContainer onto gv (name,descr,gid) =
  do (gs,_) <- readIORef gv
     case lookup gid gs of
       Nothing -> return()
       Just g ->
         do rvs <- return(A.relViewSpecs g)
            specEntries <- return(S.row (map relSpecToFormEntry rvs))
            form <- return(firstRow S.// specEntries)
            valueOpt <- S.doForm "Show relations" form
            return()
  where
    firstRow =
      (S.newFormEntry "" ()) S.\\ --
      (S.newFormEntry "Show" ()) S.\\ --
      (S.newFormEntry "Transitive" ())
    relSpecToFormEntry (A.RelViewSpec relname b1 b2) =
      (S.newFormEntry relname ()) S.\\ --
      (S.newFormEntry "" b1) S.\\ --
      (S.newFormEntry "" b2)
