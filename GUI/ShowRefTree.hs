{- |
Module      :  ./GUI/ShowRefTree.hs
Copyright   :  (c) Mihai Codescu, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mihai.codescu@dfki.de
Stability   :  provisional
Portability :  non-portable (Logic)

display the logic graph
-}

module GUI.ShowRefTree (showRefTree) where

import Control.Monad

import Data.Graph.Inductive.Graph as Tree
import Data.IORef

import GUI.GraphTypes
import GUI.UDGUtils as UDG
import GUI.Utils
import GUI.GraphLogic

import Interfaces.DataTypes
import Interfaces.Command
import Common.Consistency
import Common.DocUtils
import Driver.Options (doDump)

import Static.DevGraph
import Static.DgUtils
import Static.PrintDevGraph
import Static.History

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Char

lookup' :: (Ord a) => Map.Map a b -> a -> b
lookup' x y = Map.findWithDefault (error "lookup': key not found") y x

showRefTree :: LibFunc
showRefTree gInfo = do
  ost <- readIORef $ intState gInfo
  case i_state ost of
    Nothing -> return ()
    Just ist -> do
     let
      le = i_libEnv ist
      dg = lookup' le $ i_ln ist
     sel <- listBox "Choose a specification" $ Map.keys $ specRoots dg
     case sel of
       Nothing -> errorDialog "Error" "no specification chosen"
       Just i -> do 
        let rspName = (Map.keys $ specRoots dg) !! i
        showRefTreeAux rspName 
            (lookup' (specRoots dg) rspName)
            gInfo

showRefTreeAux :: String -> [Int] -> LibFunc
showRefTreeAux rspName roots gInfo = do
    graph <- newIORef daVinciSort
    nodesEdges <- newIORef (([], []) :: NodeEdgeListRef)
    let
      globalMenu =
        GlobalMenu (UDG.Menu Nothing
          [])
      graphParms = globalMenu $$
                   GraphTitle ("Refinement Tree of " ++ rspName) $$
                   OptimiseLayout True $$
                   AllowClose (return True) $$
                   emptyGraphParms
    graph' <- newGraph daVinciSort graphParms
    addNodesAndEdgesRef gInfo graph' nodesEdges roots
    writeIORef graph graph'
    redraw graph'

type NodeEdgeListRef = ([DaVinciNode Int], [DaVinciArc (IO RTLinkLab)])
type NodeEdgeListDep = ([DaVinciNode DiagNodeLab], [DaVinciArc (IO String)])

addNodesAndEdgesRef :: GInfo -> DaVinciGraphTypeSyn ->
                       IORef NodeEdgeListRef -> [Int] -> IO ()
addNodesAndEdgesRef gInfo@(GInfo { hetcatsOpts = opts}) graph nodesEdges roots = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let
    le = i_libEnv ist
    dg = lookup' le $ i_ln ist
    allRefTree = refTree dg
    ccomp = getConnectedComps (Set.fromList roots) allRefTree
    getConnectedComps nodes0 tree = 
     let nodes1 = concatMap (suc tree) $ Set.toList nodes0
     in if Set.isSubsetOf (Set.fromList nodes1) $ nodes0 
           then Set.toList nodes0 
           else getConnectedComps 
                  (foldl (\ s x -> Set.insert x s) nodes0 nodes1) tree
    rTree = Tree.subgraph ccomp allRefTree
    vertexes = map fst $ Tree.labNodes rTree
    isRoot n = (any (\ (_, _, llab) -> rtl_type llab == RTComp) $
                out rTree n) && not
               (any (\ (_, _, llab) -> rtl_type llab == RTComp) $
                inn rTree n)
        -- look for outgoing component links
    arcs = Tree.labEdges rTree
    subNodeMenuRoots = LocalMenu (UDG.Menu Nothing [
                   Button "Show dependency diagram" $ showDiagram gInfo dg,
                   Button "Show spec" $ showSpec dg,
                   Button "Check consistency" $ checkCons gInfo])
    subNodeMenu = LocalMenu (UDG.Menu Nothing [
                   Button "Show spec" $ showSpec dg,
                   Button "Check consistency" $ checkCons gInfo])
    subNodeTypeParmsR = subNodeMenuRoots $$$
                        Ellipse $$$
                        ValueTitle (return . rtn_name . labRT dg) $$$
                        Color (getColor opts Blue True True) $$$
                        emptyNodeTypeParms
    subNodeTypeParms = subNodeMenu $$$
                       Ellipse $$$
                       ValueTitle (return . rtn_name . labRT dg) $$$
                       Color (getColor opts Green True True) $$$
                       emptyNodeTypeParms
   subNodeType <- newNodeType graph subNodeTypeParms
   -- subNodeListI <- mapM (newNode graph subNodeType) internal
   subNodeTypeR <- newNodeType graph subNodeTypeParmsR
   subNodeList <- mapM (\ x -> if isRoot x then
                                newNode graph subNodeTypeR x
                              else newNode graph subNodeType x) vertexes
   -- let subNodeList = subNodeListI ++ subNodeListR
   let
    nodes' = Map.fromList $ zip (Tree.nodes rTree) subNodeList
    subArcMenu = LocalMenu (UDG.Menu Nothing [])
    subArcTypeParms = subArcMenu $$$
                      ValueTitle (return $ return "") $$$
                      Color (getColor opts Black False False) $$$
                      emptyArcTypeParms
    subArcTypeParmsT = subArcMenu $$$
                      ValueTitle (return $ return "") $$$
                      Color (getColor opts Blue False False) $$$
                      emptyArcTypeParms
    subArcTypeParmsR = subArcMenu $$$
                      ValueTitle (return $ return "") $$$
                      Color (getColor opts Coral False False) $$$
                      emptyArcTypeParms
   subArcType <- newArcType graph subArcTypeParms
   let insertSubArc (n1, n2, e) = newArc graph subArcType
                                            (return e)
                                            (lookup' nodes' n1)
                                            (lookup' nodes' n2)
   subArcList <- mapM insertSubArc $
                    filter (\ (_, _, e) -> rtl_type e == RTComp) arcs
   subArcTypeT <- newArcType graph subArcTypeParmsT
   let insertSubArcT (n1, n2, e) = newArc graph subArcTypeT
                                             (return e)
                                            (lookup' nodes' n1)
                                            (lookup' nodes' n2)
   subArcListT <- mapM insertSubArcT $
                    filter (\ (_, _, _e) -> False) -- TODO: it was easier
                    arcs
   subArcTypeR <- newArcType graph subArcTypeParmsR
   let insertSubArcR (n1, n2, e) = newArc graph subArcTypeR
                                            (return e)
                                            (lookup' nodes' n1)
                                            (lookup' nodes' n2)
   subArcListR <- mapM insertSubArcR $
                    filter (\ (_, _, e) -> rtl_type e == RTRefine) arcs
   writeIORef nodesEdges (subNodeList, subArcList ++ subArcListT
                                       ++ subArcListR)


checkCons :: GInfo -> Int -> IO ()
checkCons gInfo n = do
  lockGlobal gInfo
  checkConsAux gInfo [n]

checkConsAux :: GInfo -> [Int] -> IO ()
checkConsAux gInfo [] = unlockGlobal gInfo
checkConsAux gInfo (n : ns) = do
 ost <- readIORef $ intState gInfo
 case i_state ost of
  Nothing -> return ()
  Just ist -> do
   let
    le = i_libEnv ist
    dg = lookup' le $ i_ln ist
    rtlab = labRT dg n
    rt = refTree dg
    changeConsStatus x = let
        oldLab = labDG dg x
        oldNInfo = nodeInfo oldLab
        newLab = oldLab {nodeInfo = case oldNInfo of
                                     DGNode o _ -> DGNode o $ mkConsStatus Cons
                                     _ -> oldNInfo}
       in [SetNodeLab oldLab (x, newLab)]
    consLinks (s, t, l) = let
        l' = l {dgl_type = case dgl_type l of
                           ScopedLink a b _ ->
                              ScopedLink a b $ mkConsStatus Cons
                           dt -> dt}
       in [DeleteEdge (s, t, l), InsertEdge (s, t, l')]
    updateDG changes = do
     let dg' = changesDGH dg changes
         history = snd $ splitHistory dg dg'
         le' = Map.insert (i_ln ist) dg' le
         lln = map DgCommandChange $ calcGlobalHistory le le'
         nst = add2history HelpCmd ost lln
         nwst = nst { i_state = Just ist { i_libEnv = le'}}
     doDump (hetcatsOpts gInfo) "PrintHistory" $ do
             putStrLn "History"
             print $ prettyHistory history
     writeIORef (intState gInfo) nwst
     updateGraph gInfo (reverse $ flatHistory history)
   case rtn_type rtlab of
     RTRef n' -> checkConsAux gInfo $ n' : ns
     RTPlain usig ->
      let units = map (\ (_, x, _) -> x) $
                 filter (\ (_ss, _tt, ll) -> rtl_type ll == RTComp) $ out rt n
      in case units of
          [] -> -- n is itself a unit, insert obligation
             case usig of
              UnitSig [] nsig _ -> do -- non-parametric unit, change node
               let gn = getNode nsig
                   changes = changeConsStatus gn
               updateDG changes
               checkConsAux gInfo ns
              UnitSig _ _ Nothing -> error "consCheck2"
              UnitSig _nsigs nsig (Just usig') -> do
                let ss = getNode usig'
                    tt = getNode nsig
                    lEdges = filter (\ (x, y, _) -> x == ss && y == tt)
                              $ labEdges $ dgBody dg
                    ll = if null lEdges then
                            error "consCheck1"
                         else head lEdges   -- parametric unit, change edge
                    changes = consLinks ll
                updateDG changes
                checkConsAux gInfo ns
          _ -> checkConsAux gInfo $ units ++ ns

showSpec :: DGraph -> Int -> IO ()
showSpec dg n =
    createTextDisplay "" (showDoc (labRT dg n) "")

showDiagram :: GInfo -> DGraph -> Int -> IO ()
showDiagram gInfo dg n = do
 let asDiags = archSpecDiags dg
     rtlab = labRT dg n
     name = rtn_diag rtlab
 when (name `elem` Map.keys asDiags) $ do
      graph <- newIORef daVinciSort
      nodesEdges <- newIORef (([], []) :: NodeEdgeListDep)
      let
       globalMenu =
        GlobalMenu (UDG.Menu Nothing
          [])
       graphParms = globalMenu $$
                   GraphTitle ("Dependency Diagram for " ++ name) $$
                   OptimiseLayout True $$
                   AllowClose (return True) $$
                   emptyGraphParms
      graph' <- newGraph daVinciSort graphParms
      addNodesAndEdgesDeps dg (Map.findWithDefault (error "showDiagram")
                            name asDiags)
                           graph' gInfo nodesEdges
      writeIORef graph graph'
      redraw graph'
 
showDiagSpec :: DGraph -> DiagNodeLab -> IO ()
showDiagSpec dg l = do
 let NodeSig n _ = dn_sig l
     nlab = labDG dg n
     g1 = globOrLocTh nlab
 createTextDisplay ""
   $ "Desc:\n" ++ dn_desc l ++ "\n" ++
    "Sig:\n" ++ showDoc g1 ""

addNodesAndEdgesDeps :: DGraph -> Diag -> DaVinciGraphTypeSyn -> GInfo ->
                       IORef NodeEdgeListDep -> IO ()
addNodesAndEdgesDeps dg diag graph gi nodesEdges = do
   let
    opts = hetcatsOpts gi
    vertexes = map snd $ Tree.labNodes $ diagGraph diag
    arcs = Tree.labEdges $ diagGraph diag
    subNodeMenu = LocalMenu (UDG.Menu Nothing [Button "Show desc and sig" $
                                showDiagSpec dg ])
    subNodeTypeParms = subNodeMenu $$$
                       Ellipse $$$
                       ValueTitle (return . (\ x ->
                                   take 20 (filter (\c -> isAlphaNum c || isSpace c) $ dn_desc x) ++ "..." )) $$$
                       Color (getColor opts Green True True) $$$
                       emptyNodeTypeParms
   subNodeType <- newNodeType graph subNodeTypeParms
   subNodeList <- mapM (newNode graph subNodeType) vertexes
   let
    nodes' = Map.fromList $ zip (Tree.nodes $ diagGraph diag) subNodeList
    subArcMenu = LocalMenu (UDG.Menu Nothing [])
    subArcTypeParms = subArcMenu $$$
                      ValueTitle (return $ return "") $$$
                      Color (getColor opts Black False False) $$$
                      emptyArcTypeParms
   subArcType <- newArcType graph subArcTypeParms
   let insertSubArc (n1, n2, _e) = newArc graph subArcType
                                            (return "")
                                            (lookup' nodes' n1)
                                            (lookup' nodes' n2)
   subArcList <- mapM insertSubArc arcs
   writeIORef nodesEdges (subNodeList, subArcList)
