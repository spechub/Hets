module GUI.ShowLogicGraph
where
 
-- for graph display
import DaVinciGraph
import GraphDisp
import GraphConfigure

-- for windows display
import TextDisplay
import Configuration
import qualified HTk
import Channels

--  data structure
import Comorphisms.LogicGraph
import Comorphisms.LogicList
import Logic.Grothendieck
import Logic.Logic
import Logic.Comorphism
-- import Logic.Provers

import qualified Common.Lib.Map as Map
import Concurrent
import Maybe
import Debug(debug)
import Events
import Destructible

showLogicGraph ::
   (GraphAllConfig graph graphParms node nodeType nodeTypeParms
      arc arcType arcTypeParms)
   => (Graph graph graphParms node nodeType nodeTypeParms
         arc arcType arcTypeParms)
   -> IO ()
showLogicGraph
   (displaySort ::
       GraphDisp.Graph graph graphParms node nodeType nodeTypeParms arc 
          arcType arcTypeParms) =
    do 
       let graphParms = GraphTitle "Logic Graph" $$
                        OptimiseLayout True $$
                        emptyGraphParms
           disp s tD = debug (s ++ (show tD))

           (nullNodeParms :: nodeTypeParms AnyLogic) = emptyNodeTypeParms
	   (nullArcTypeParms :: arcTypeParms [Char]) = emptyArcTypeParms

       logicG <- newGraph displaySort graphParms
       
       (killChannel :: Channel ()) <- newChannel   

       let logicNodeMenu = LocalMenu(Button "Type" (disp "Type"))  -- ??
           logicNodeTypeParms = 
               logicNodeMenu $$$
               Triangle $$$
               ValueTitle (\l -> case l of
                                   Logic lid -> 
                                    return (language_name lid)) $$$
               Color "green" $$$
               nullNodeParms
      
       nodeType <- newNodeType logicG logicNodeTypeParms
                 
       -- Erzeugung der Knoten (in einer liste)
       nodeList <- mapM (newNode logicG nodeType) (Map.elems(logics logicGraph))

       -- Erstellung der Abbildung der Namen und der Knoten.
       let namesAndNodes = Map.fromList (zip (Map.keys(logics logicGraph)) nodeList)
       
           lookupLogic(Logic lid) = fromJust (Map.lookup (language_name lid) namesAndNodes)
           logicArcMenu = LocalMenu(Button "Type" (disp "Type"))
           normalArcTypeParms = logicArcMenu $$$
                                Color "black" $$$
                                nullArcTypeParms
                            
           inclArcTypeParms = logicArcMenu $$$
                               Color "blue" $$$
                               nullArcTypeParms
                  
       normalArcType <- newArcType logicG normalArcTypeParms
       inclArcType   <- newArcType logicG inclArcTypeParms   
       
       let insertComo = 
             (\c -> 
                case c of
                  Comorphism cid ->
                    newArc logicG normalArcType "ArcType" (lookupLogic(Logic(sourceLogic cid))) (lookupLogic(Logic(targetLogic cid))))   
           insertIncl =
             (\i -> 
                case i of
                  Comorphism cid -> 
                    newArc logicG inclArcType "ArcType" (lookupLogic(Logic(sourceLogic cid))) (lookupLogic(Logic(targetLogic cid)))) 
       arcList1 <- mapM insertComo (Map.elems(comorphisms logicGraph))
       arcList2 <- mapM insertIncl (Map.elems(inclusions logicGraph)) 
       
       redraw logicG
       
       sync(
            (receive killChannel) >>> 
               do
                  putStrLn "Destroy graph"
                  destroy logicG
               
         +> (destroyed logicG)
        )