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
import Logic.Grothendieck
import Logic.Logic
import Logic.Comorphism
import Logic.Prover

import qualified Common.Lib.Map as Map
-- import Concurrent
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

       let logicNodeMenu = LocalMenu(Menu (Just "Info") 
               [Button "Parser" (\lg -> createTextDisplay ("Parsers of " ++ showTitle lg) (showParse lg) [size(80,40)]),
                Button "Sublogic" (\lg -> createTextDisplay ("Sublogics of " ++ showTitle lg) (showSubLogic lg) [size(80,40)]),
                Button "Prover" (\lg -> createTextDisplay ("Provers of " ++ showTitle lg) (showProver lg) [size(80,40)]),
                Button "Cons_checker" (\lg -> createTextDisplay ("Cons_Checkers of " ++ showTitle lg) (showConsChecker lg) [size(80,40)])])
           
           logicNodeTypeParms = 
               logicNodeMenu $$$
               Ellipse $$$
               ValueTitle (return . showTitle) $$$
               Color "green" $$$
               nullNodeParms
      
       nodeType <- newNodeType logicG logicNodeTypeParms
                 
       -- Erzeugung der Knoten (in einer liste)
       nodeList <- mapM (newNode logicG nodeType) (Map.elems(logics logicGraph))

       -- Erstellung der Abbildung der Namen und der Knoten.
       let namesAndNodes = Map.fromList (zip (Map.keys(logics logicGraph)) nodeList)
       
           lookupLogic(Logic lid) = fromJust (Map.lookup (language_name lid) namesAndNodes)
           logicArcMenu = LocalMenu(Button "Como" (disp "Como"))
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

       arcList1 <- mapM insertIncl (Map.elems(inclusions logicGraph))
       arcList2 <- mapM insertComo  [rest | rest <- Map.elems(comorphisms logicGraph), not (rest `elem` (Map.elems(inclusions logicGraph)))] 
                  --(drop (length arcList1) (Map.elems (comorphisms logicGraph)))
       
       
       redraw logicG
       
       sync(
            (receive killChannel) >>> 
               do
                  putStrLn "Destroy graph"
                  destroy logicG
               
         +> (destroyed logicG)
        )

  where showParse l = 
	    case l of 
               Logic lid -> let s1 =  case parse_basic_spec lid of
				      Just _  -> "Parser for basic specifications.\n"
				      Nothing -> ""
				s2 =  case parse_symb_items lid of
				      Just _ ->  "Parser for symbol lists.\n"
				      Nothing -> ""
				s3 =  case parse_symb_map_items lid of
				      Just _ ->  "Parser for symbol maps.\n"
				      Nothing -> ""
				s4 =  case parse_sentence lid of
				      Just _ ->  "Parser for sentences.\n"
				      Nothing -> ""
				s5 =  case basic_analysis lid of
				      Just _ ->  "Analysis of basic specifications.\n"
                                      Nothing -> ""
                                s6 =  case data_logic lid of	       
				      Just _ ->  "is a process logic.\n" 
				      Nothing -> ""
			     in  (s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6)
	 
        showSubLogic l = 
            case l of
              Logic lid -> unlines (map unwords $ 
                                map (sublogic_names lid) (all_sublogics lid))
        showTitle l = 
            case l of
              Logic lid -> language_name lid

        showProver l = 
            case l of
              Logic lid -> unlines $ map prover_name (provers lid)

        showConsChecker l = 
            case l of
              Logic lid -> unlines $ map cons_checker_name (cons_checkers lid)