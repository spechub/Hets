{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang and Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (Logic)

display the logic graph
-}

module GUI.ShowLogicGraph (showPlainLG, showLG) where

import GUI.UDGUtils as UDG
import GUI.HTkUtils as HTk
import qualified GUI.GraphAbstraction as GA

import HTk.Toolkit.DialogWin (useHTk)

import Comorphisms.LogicGraph
import Comorphisms.LogicList
import Comorphisms.HetLogicGraph
import Logic.Grothendieck
import Logic.Logic
import Logic.Comorphism
import Logic.Prover

import qualified Data.Map as Map
import Data.List
import qualified Common.Lib.Rel as Rel
import Common.Consistency

import Data.Typeable

graphParms :: GraphAllConfig graph graphParms node nodeType nodeTypeParms
                              arc arcType arcTypeParms
           => Graph graph graphParms node nodeType nodeTypeParms
                        arc arcType arcTypeParms
           -> String -- ^ title of graph
           -> graphParms
graphParms _ title =
             GraphTitle title $$
             OptimiseLayout True $$
             AllowClose (return True) $$
             emptyGraphParms

makeNodeMenu :: (GraphAllConfig graph graphParms node
                                    nodeType nodeTypeParms
                                     arc arcType arcTypeParms,
                       Typeable value)
                  => Graph graph graphParms node nodeType nodeTypeParms
                        arc arcType arcTypeParms
                  -> (value -> IO String)
                  -- ^ display the value as a String
                  -> LocalMenu value
                  -> String -- ^ color of node
                  -> nodeTypeParms value
makeNodeMenu _ showMyValue logicNodeMenu color =
               logicNodeMenu $$$
               Ellipse $$$
               ValueTitle showMyValue $$$
               Color color $$$
               emptyNodeTypeParms

stableColor, testingColor, unstableColor, experimentalColor,
   proverColor :: String
stableColor = "#00FF00"
testingColor = "#88FF33"
unstableColor = "#CCFF66"
experimentalColor = "white"
proverColor = "lightsteelblue"

normalArcColor :: String
normalArcColor = "black"

inclusionArcColor :: String
inclusionArcColor = "blue"

-- | Test whether a comorphism is an ad-hoc inclusion
isInclComorphism :: AnyComorphism -> Bool
isInclComorphism (Comorphism cid) =
    Logic (sourceLogic cid) == Logic (targetLogic cid) &&
    isProperSublogic (G_sublogics (sourceLogic cid) (sourceSublogic cid))
                      (G_sublogics (targetLogic cid) (targetSublogic cid))

showLogicGraph :: Bool -> IO GA.OurGraph
showLogicGraph plain = do
           -- disp s tD = debug (s ++ (show tD))
       logicG <- newGraph daVinciSort
                $ (if plain then (GlobalMenu (UDG.Menu Nothing [
                Button "Show detailed logic graph" showHSG ]) $$)
                else id)
                $ graphParms daVinciSort $ if plain then "Logic Graph" else
                  "Heterogeneous Sublogic Graph"
       let logicNodeMenu = LocalMenu $ UDG.Menu (Just "Info")
                $ [Button "Tools" $ \ slg -> let lg = toAnyLogic slg in
                      createTextDisplay
                      ("Parsers, Provers and Cons_Checker of "
                       ++ show lg) (showTools lg) [size (80, 25)]]
                ++ [Button "Sublogic" $ \ slg -> let lg = toAnyLogic slg in
                       createTextDisplay ("Sublogics of "
                       ++ show lg) (showSublogic lg) [size (80, 25)] | plain]
                ++ [Button "Sublogic Graph" $ showSubLogicGraph . toAnyLogic,
                Button "Description" $ \ slg -> let lg = toAnyLogic slg in
                      createTextDisplay
                      ("Description of " ++ show lg) (showDescription lg)
                                      [size (83, 25)]]
           makeLogicNodeMenu = makeNodeMenu daVinciSort
             (return . if plain then show . toAnyLogic else show)
                            logicNodeMenu
       stableNodeType <- newNodeType logicG $ makeLogicNodeMenu stableColor
       testingNodeType <- newNodeType logicG $ makeLogicNodeMenu testingColor
       unstableNodeType <- newNodeType logicG $ makeLogicNodeMenu unstableColor
       experimentalNodeType <- newNodeType logicG $
                               makeLogicNodeMenu experimentalColor
       proverNodeType <-
           newNodeType logicG $ makeLogicNodeMenu proverColor
       let newNode' logic =
             case toAnyLogic logic of
               Logic lid -> if null $ provers lid then let
                   nodeType = case stability lid of
                     Stable -> stableNodeType
                     Testing -> testingNodeType
                     Unstable -> unstableNodeType
                     Experimental -> experimentalNodeType
                   in newNode logicG nodeType logic
                 else newNode logicG proverNodeType logic
           myMap = if plain then Map.map (\ (Logic l) ->
                                          G_sublogics l $ top_sublogic l)
                     $ Map.fromList $ map addLogicName
                     $ Map.elems $ logics logicGraph
                   else sublogicNodes hetSublogicGraph

       -- production of the nodes (in a list)
       nodeList <- mapM newNode' $ Map.elems myMap
       -- build the map with the node's name and the node.
       let namesAndNodes = Map.fromList (zip (Map.keys myMap)
                                             nodeList)
           lookupLogi gslStr =
               Map.findWithDefault (error "lookupLogi: Logic not found")
                                   gslStr
                                   namesAndNodes
           {- each edge can also show the informations (the
             description of comorphism and names of
             source/target-Logic as well as the sublogics). -}
           logicArcMenu =
               LocalMenu $ Button "Info"
                 $ \ c -> createTextDisplay (show c) (showComoDescription c)
                              [size (80, 25)]
           acmName (Comorphism cid) = return $ language_name cid
           normalArcTypeParms = logicArcMenu $$$         -- normal comorphism
                                Color normalArcColor $$$
                                ValueTitle acmName $$$
                                emptyArcTypeParms
           insertArcType tp ((src, trg), acm) =
                  newArc logicG tp acm (lookupLogi src) (lookupLogi trg)
           inclArcTypeParms = logicArcMenu $$$           -- inclusion
                               Color inclusionArcColor $$$
                               (if plain then id else (ValueTitle acmName $$$))
                               emptyArcTypeParms
       normalArcType <- newArcType logicG normalArcTypeParms
       inclArcType <- newArcType logicG inclArcTypeParms
       if plain then do
         let toPair co@(Comorphism c) = ((language_name (sourceLogic c)
               , language_name (targetLogic c)), co)
             insertComo = insertArcType normalArcType . toPair -- for cormophism
             insertIncl = insertArcType inclArcType . toPair   -- for inclusion
         mapM_ insertIncl inclusionList
         mapM_ insertComo $ filter (`notElem` inclusionList) comorphismList
        else do
         let (inclCom, notInclCom) =
               partition ((`elem` inclusionList) . snd) $
               concatMap (\ (x, ys) -> zip (repeat x) ys) $
                   Map.toList -- [((String,String),[AnyComorphism])]
                          (comorphismEdges hetSublogicGraph)
             (adhocCom, normalCom) =
               partition (isInclComorphism . snd) notInclCom
             adhocInclArcTypeParms =
                             Color inclusionArcColor $$$ -- ad-hoc inclusion
                             emptyArcTypeParms
         adhocInclArcType <- newArcType logicG adhocInclArcTypeParms
         mapM_ (insertArcType inclArcType) inclCom
         mapM_ (insertArcType adhocInclArcType) adhocCom
         mapM_ (insertArcType normalArcType) normalCom
       redraw logicG
       return logicG

showSubLogicGraph :: AnyLogic -> IO ()
showSubLogicGraph subl =
          case subl of
            Logic sublid ->
              do subLogicG <- newGraph daVinciSort
                   $ graphParms daVinciSort "SubLogic Graph"
                 let listG_Sublogics = all_sublogics sublid
                     subNodeMenu = LocalMenu (UDG.Menu Nothing [])
                     subNodeTypeParms =
                         subNodeMenu $$$
                         Ellipse $$$
                         ValueTitle (return . sublogicName) $$$
                         Color "yellow" $$$
                         emptyNodeTypeParms
                 subNodeType <- newNodeType subLogicG subNodeTypeParms
                 subNodeList <- mapM (newNode subLogicG subNodeType)
                                listG_Sublogics
                 let slAndNodes = Map.fromList $
                                  zip listG_Sublogics subNodeList
                     lookupSublogic g_sl =
                         Map.findWithDefault
                              (error "lookupSublogic: node not found")
                              g_sl slAndNodes
                     subArcMenu = LocalMenu (UDG.Menu Nothing [])
                     subArcTypeParms = subArcMenu $$$
                                       Color "green" $$$
                                       emptyArcTypeParms
                 subArcType <- newArcType subLogicG subArcTypeParms
                 let insertSubArc (node1, node2) =
                           newArc subLogicG subArcType ""
                                  (lookupSublogic node1)
                                  (lookupSublogic node2)
                     subl_nodes =
                         Rel.toList $ Rel.intransKernel $ Rel.fromList
                          [ (g1, g2)
                            | g1 <- listG_Sublogics
                            , g2 <- listG_Sublogics
                            , g1 /= g2
                            , isSubElem g1 g2
                          ]
                 mapM_ insertSubArc subl_nodes
                 redraw subLogicG

toAnyLogic :: G_sublogics -> AnyLogic
toAnyLogic (G_sublogics lid _) = Logic lid

showSublogic :: AnyLogic -> String
showSublogic (Logic lid) = unlines (map sublogicName (all_sublogics lid))

showSubTitle :: G_sublogics -> String
showSubTitle (G_sublogics _ lid) = sublogicName lid

showDescription :: AnyLogic -> String
showDescription (Logic lid) = let s = description lid in
    (if null s then "No description available" else s) ++ "\n\nStability: "
    ++ show (stability lid)

showComoDescription :: AnyComorphism -> String
showComoDescription (Comorphism cid) =
  let ssid = G_sublogics (sourceLogic cid) (sourceSublogic cid)
      tsid = G_sublogics (targetLogic cid) (targetSublogic cid)
      s = description cid
  in (if null s then "" else s ++ "\n\n")
  ++ "source logic:     " ++ language_name (sourceLogic cid) ++ "\n\n"
  ++ "target logic:     " ++ language_name (targetLogic cid) ++ "\n"
  ++ "source sublogic:  " ++ showSubTitle ssid ++ "\n"
  ++ "target sublogic:  " ++ showSubTitle tsid

showTools :: AnyLogic -> String
showTools (Logic li) =
    case Map.keys $ parsersAndPrinters li of
      s@(_ : r) -> "Parser for basic specifications.\n"
        ++ if null r then "" else
           unlines . filter (not . null) $ "Additional serializations:"
             : map show s
      [] -> ""
  ++ case parse_symb_items li of
       Just _ -> "Parser for symbol lists.\n"
       Nothing -> ""
  ++ case parse_symb_map_items li of
       Just _ -> "Parser for symbol maps.\n"
       Nothing -> ""
  ++ case basic_analysis li of
       Just _ -> "Analysis of basic specifications.\n"
       Nothing -> ""
  ++ case data_logic li of
       Just _ -> "is a process logic.\n"
       Nothing -> ""
  ++ case provers li of
       [] -> ""
       ls -> unlines $ "\nProvers:" : map proverName ls
  ++ case cons_checkers li of
       [] -> ""
       ls -> unlines $ "\nConsistency checkers:" : map ccName ls
  ++ case conservativityCheck li of
       [] -> ""
       ls -> unlines $ "\nConservatity checkers:" : map checkerId ls


showHSG :: IO ()
showHSG = showLogicGraph False >> return ()

showLG :: IO ()
showLG = showLogicGraph True >> return ()

showPlainLG :: IO ()
showPlainLG = do
  wishInst <- HTk.initHTk [HTk.withdrawMainWin]
  useHTk
  lg <- showLogicGraph True
  sync (destroyed lg)
  destroy wishInst
