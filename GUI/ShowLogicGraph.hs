{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang and Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  non-portable (Logic)

display the logic graph
-}

module GUI.ShowLogicGraph where

-- for graph display
import DaVinciGraph
import GraphDisp
import GraphConfigure

-- for windows display
import TextDisplay
import Configuration

--  data structure
import Comorphisms.LogicGraph
import Logic.Grothendieck
import Logic.Logic
import Logic.Comorphism
import Logic.Prover
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel


showLogicGraph ::
   (GraphAllConfig graph graphParms node nodeType nodeTypeParms
      arc arcType arcTypeParms)
   => (Graph graph graphParms node nodeType nodeTypeParms
         arc arcType arcTypeParms)
   -> IO ()
showLogicGraph
   (displaySrt ::
       GraphDisp.Graph graph graphParms node nodeType nodeTypeParms arc
          arcType arcTypeParms) =
    do
       let graphParms = GraphTitle "Logic Graph" $$
                        OptimiseLayout True $$
                        AllowClose (return True) $$
                        emptyGraphParms
           -- disp s tD = debug (s ++ (show tD))
       logicG <- newGraph displaySrt graphParms
       let logicNodeMenu = LocalMenu(Menu (Just "Info")
               [Button "Tools" (\lg -> createTextDisplay
                      ("Parsers, Provers and Cons_Checker of "
                       ++ showTitle lg) (showTools lg) [size(80,25)]),
                Button "Sublogic" (\lg -> createTextDisplay ("Sublogics of "
                       ++ showTitle lg) (showSublogic lg) [size(80,25)]),
                Button "Sublogic Graph" (\lg -> showSubLogicGraph displaySrt
                                                lg),
                Button "Description" (\lg -> createTextDisplay
                      ("Description of " ++ showTitle lg) (showDescription lg)
                                      [size(83,25)])
               ])
           makeLogicNodeMenu color =
               logicNodeMenu $$$
               Ellipse $$$
               ValueTitle (return . showTitle) $$$
               Color color $$$
               nullNodeParms
       stableNodeType <- newNodeType logicG $ makeLogicNodeMenu "#00FF00"
       testingNodeType <- newNodeType logicG $ makeLogicNodeMenu "#88FF33"
       unstableNodeType <- newNodeType logicG $ makeLogicNodeMenu "#CCFF66"
       experimentalNodeType <- newNodeType logicG $ makeLogicNodeMenu "white"
       proverNodeType <-
           newNodeType logicG $ makeLogicNodeMenu "lightsteelblue"
       let newNode' logic =
             case logic of
                  Logic lid -> if (hasProver lid) then
                                      newNode logicG proverNodeType logic
                               else let nodeType = case stability lid of
                                         Stable -> stableNodeType
                                         Testing -> testingNodeType
                                         Unstable -> unstableNodeType
                                         Experimental -> experimentalNodeType
                                      in newNode logicG nodeType logic
             where hasProver lid =
                       not $ null $ provers lid

       -- production of the nodes (in a list)
       nodeList <- mapM newNode' (Map.elems(logics logicGraph))
       -- build the map with the node's name and the node.
       let namesAndNodes = Map.fromList (zip (Map.keys(logics logicGraph))
                                             nodeList)
           lookupLogi (Logic lid) = 
               Map.findWithDefault (error "lookupLogi: Logic not found") 
                                   (language_name lid)
                                   namesAndNodes
           {- each edge can also show the informations (the
             description of comorphism and names of
             source/target-Logic as well as the sublogics). -}
           logicArcMenu =
               LocalMenu(Button "Info"
                 (\c -> case c of
                         Comorphism cid ->
                          let ssid = G_sublogics (sourceLogic cid)
                                     (sourceSublogic cid)
                              tsid = G_sublogics (targetLogic cid)
                                     (targetSublogic cid)
                          in  createTextDisplay (show c)
                                  (showComoDescription c ++ "\n\n" ++
                              "source logic:     " ++
                                   (language_name $ sourceLogic cid) ++
                              "\n\n" ++
                              "target logic:     " ++
                                   (language_name $ targetLogic cid) ++
                              "\n" ++
                              "source sublogic:  " ++ showSubTitle ssid ++
                                   "\n" ++
                              "target sublogic:  " ++ showSubTitle tsid)
                              [size(80,25)]))
           normalArcTypeParms = logicArcMenu $$$         -- normal comorphism
                                Color "black" $$$
                                ValueTitle (\c -> case c of
                                    Comorphism cid ->
                                        return $ language_name cid) $$$
                                nullArcTypeParms
           inclArcTypeParms = logicArcMenu $$$           -- inclusion
                               Color "blue" $$$
                               nullArcTypeParms
       normalArcType <- newArcType logicG normalArcTypeParms
       inclArcType   <- newArcType logicG inclArcTypeParms
       let insertComo =            -- for cormophism
             (\c ->
                case c of
                  Comorphism cid ->
                    let sid = Logic (sourceLogic cid)
                        tid = Logic (targetLogic cid)
                    in  newArc logicG normalArcType c (lookupLogi sid)
                            (lookupLogi tid))
           insertIncl =            -- for inclusion
             (\i ->
                case i of
                  Comorphism cid ->
                    let sid = Logic (sourceLogic cid)
                        tid = Logic (targetLogic cid)
                    in  newArc logicG inclArcType i (lookupLogi sid)
                            (lookupLogi tid))
       mapM_ insertIncl (Map.elems(inclusions logicGraph))
       mapM_ insertComo
                   [ rest | rest <- Map.elems(comorphisms logicGraph)
                   , not (rest `elem` (Map.elems(inclusions logicGraph)))]
       redraw logicG
    where
        (nullNodeParms :: nodeTypeParms AnyLogic) = emptyNodeTypeParms
        (nullArcTypeParms :: arcTypeParms AnyComorphism) = emptyArcTypeParms
        (nullSubArcTypeParms:: arcTypeParms [Char]) = emptyArcTypeParms
        showSublogic l =
            case l of
              Logic lid -> unlines (map unwords $
                                map sublogic_names (all_sublogics lid))
        showSubTitle gsl =
            case gsl of
              G_sublogics _ sls -> unwords $ sublogic_names sls
        showTitle l =
            case l of
              Logic lid -> language_name lid
        showDescription l =
            case l of
              Logic lid -> description lid ++
                           "\n\nStability: " ++ show (stability lid)
        showComoDescription c =
            case c of
              Comorphism cid -> description cid
        showTools lg =
           case lg of
                Logic lid -> showParse lid ++ "\nProvers: " ++ showProver lid
                     ++ "\nConsistency checkers: " ++ showConsChecker lid
           where
             showProver lid = if null (provers lid) then "None"
                               else unlines $ map prover_name (provers lid)

             showConsChecker lid = if null (cons_checkers lid) then "None"
                        else unlines $ map prover_name (cons_checkers lid)
             showParse lid =
                   let s1 =  case parse_basic_spec lid of
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
        showSubLogicGraph
           (displaySort' :: GraphDisp.Graph graph graphParms node nodeType
            nodeTypeParms arc arcType arcTypeParms) subl =
          case subl of
            Logic sublid ->
              do let graphParms = GraphTitle "SubLogic Graph" $$
                                             OptimiseLayout True $$
                                             AllowClose (return True) $$
                                             emptyGraphParms
                 subLogicG <- newGraph displaySort' graphParms
                 let listG_Sublogics = -- map (\sbl -> G_sublogics sublid sbl)
                                       (all_sublogics sublid)
                     subNodeMenu = LocalMenu (Menu Nothing [])
                     subNodeTypeParms =
                         subNodeMenu $$$
                         Ellipse $$$
                         ValueTitle
                           (\gsl -> return (unwords $ sublogic_names gsl)) $$$
                         Color "yellow" $$$
                         emptyNodeTypeParms
                 subNodeType <- newNodeType subLogicG subNodeTypeParms
                 subNodeList <- mapM (newNode subLogicG subNodeType)
                                listG_Sublogics
                 let slAndNodes = Map.fromList $ 
                                  zip (map sublogic_names listG_Sublogics) 
                                      subNodeList
                     lookupSublogic g_sl = 
                         Map.findWithDefault 
                              (error "lookupSublogic: node not found") 
                              g_sl slAndNodes
                     subArcMenu = LocalMenu( Menu Nothing [])
                     subArcTypeParms = subArcMenu $$$
                                       Color "green" $$$
                                       nullSubArcTypeParms
                 subArcType <- newArcType subLogicG subArcTypeParms
                 let insertSubArc = \ (node1, node2) ->
                           newArc subLogicG subArcType "" 
                                  (lookupSublogic node1) 
                                  (lookupSublogic node2)
                     subl_nodes = 
                         Rel.toList $ Rel.intransKernel $ Rel.fromList
                          [ (sublogic_names g1, sublogic_names g2)
                            | g1 <- listG_Sublogics
                            , g2 <- listG_Sublogics
                            , g1 /= g2
                            , isSubElem g1 g2
                          ]
                 mapM_ insertSubArc subl_nodes 
                 redraw subLogicG

showLG :: IO ()
showLG = showLogicGraph daVinciSort
