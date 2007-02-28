
module GUI.ShowLibGraph
  (showLibGraph)
where

import Syntax.AS_Library(LIB_NAME)
import Static.DevGraph

-- for graph display
import DaVinciGraph
import GraphDisp
import GraphConfigure

-- for windows display
import TextDisplay()
import Configuration
import Events
import Destructible
import qualified HTk

import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
--import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Graph as Tree

import Data.List


showLibGraph :: LibEnv -> IO ()
showLibGraph le =
  do
    let
      graphParms = GraphTitle "Library Graph" $$
		   OptimiseLayout True $$
		   AllowClose (return True) $$
		   emptyGraphParms
    wishInst <- HTk.initHTk [HTk.withdrawMainWin]
    depG <- newGraph daVinciSort graphParms
    let 
      subNodeMenu = LocalMenu( Menu Nothing [])
      subNodeTypeParms = subNodeMenu $$$
			 Ellipse $$$
			 ValueTitle return $$$
			 Color "yellow" $$$
			 emptyNodeTypeParms
    subNodeType <- newNodeType depG subNodeTypeParms
    let
      keys = Map.keys le
    subNodeList <- mapM ((newNode depG subNodeType).show) keys
    let
      nodes = Map.fromList $ zip keys subNodeList
      lookup' x = Map.findWithDefault
                    (error "lookup': node not found")
                    x nodes
      subArcMenu = LocalMenu( Menu Nothing [])
      subArcTypeParms = subArcMenu $$$
                        ValueTitle id $$$
                        Color "green" $$$
                        emptyArcTypeParms
    subArcType <- newArcType depG subArcTypeParms
    let
      insertSubArc = \ (node1, node2) ->
                          newArc depG subArcType (return "")
                            (lookup' node1)
                            (lookup' node2)
    mapM_ insertSubArc $
      Rel.toList $ Rel.intransKernel $ Rel.transClosure $
      Rel.fromList $ getLibDeps le
    redraw depG
    sync(destroyed depG)
    destroy wishInst
    HTk.finishHTk

getLibDeps :: LibEnv -> [(LIB_NAME, LIB_NAME)]
getLibDeps le =
  concat $ map (getDep le) $ Map.keys le
  where
    getDep :: LibEnv -> LIB_NAME -> [(LIB_NAME, LIB_NAME)]
    getDep le ln =
      map (\ x -> (ln, x)) $ map (\ (_,x,_) -> dgn_libname x) $ IntMap.elems $
        IntMap.filter (\ (_,x,_) -> isDGRef x) $ Tree.convertToMap $ 
        devGraph $ lookupGlobalContext ln le
