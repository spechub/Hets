{- |
Module      :  $Header$
Copyright   :  (c) jianchun wang and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  wjch868@tzi.de
Stability   :  provisional
Portability :  portable

-}
module Main where

-- for graph display
import DaVinciGraph
import GraphDisp
import GraphConfigure

-- for windows display
import TextDisplay
import Configuration
import Events
import Destructible
import qualified HTk

import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel

import System.Directory
import Data.List
import Common.Utils

main :: IO ()
main = do
    fs <- getDirectoryContents "."
    let suf = ".imports"
        fn = filter (isSuffixOf suf) fs
        ffn = map (fst . stripSuffix [suf]) fn
        ffnn = filter (\ s -> all (not . (`isSublistOf` s)) excludes) 
                 $ filter (elem '.') ffn
        fln = map (fst . break (== '.'))  ffnn 
        fln' = nub fln
    lfs <- mapM (readFile . (++ suf)) ffnn
    let ss = map (filter (isPrefixOf "import") . lines) lfs
        sss = getContent6 ss
        ssss' = map (filter (\ s -> all (not . (`isSublistOf` s)) excludes))
                    sss 
        ssss = map (map $ fst . break (== '.')) ssss'
        sss' = map nub ssss
        graphParms = GraphTitle "Dependency Graph" $$
                        OptimiseLayout True $$
                        AllowClose (return True) $$
                        emptyGraphParms
    wishInst <- HTk.initHTk [HTk.withdrawMainWin]
    depG <- newGraph daVinciSort graphParms
    let flln = nub $ fln' ++ concat sss'
        subNodeMenu = LocalMenu (Menu (Just "Info") [
                      Button "Contents" (\lg -> createTextDisplay 
                      ("Contents of " ++ lg) 
                       (showCon lg) [size(80,25)])])
        showCon lg = unlines (filter (isPrefixOf (lg++".")) ffnn)
        subNodeTypeParms =
                         subNodeMenu $$$
                         Ellipse $$$
                         ValueTitle return $$$
                         Color "yellow" $$$
                         emptyNodeTypeParms
    subNodeType <- newNodeType depG subNodeTypeParms
    subNodeList <- mapM (newNode depG subNodeType) flln
    let slAndNodes = Map.fromList $ zip flln subNodeList
        lookup' g_sl = Map.findWithDefault 
                              (error "lookup': node not found") 
                              g_sl slAndNodes
        subArcMenu = LocalMenu( Menu Nothing [])
        subArcTypeParms = subArcMenu $$$
                          ValueTitle id $$$
                            Color "green" $$$
                          emptyArcTypeParms
    subArcType <- newArcType depG subArcTypeParms
    let insertSubArc = \ (node1, node2) ->
                           newArc depG subArcType (return "") 
                                  (lookup' node1) 
                                  (lookup' node2)
    mapM_ insertSubArc $ 
                     Rel.toList $ Rel.intransKernel $ Rel.transClosure $ 
                        Rel.fromList
                     $ isIn3 $ concat $ zipWith getContent2 fln sss'
    redraw depG
    sync(destroyed depG)
    destroy wishInst
    HTk.finishHTk

excludes :: [String]
excludes = 
    [ "ATC", ".CreateTheories" -- Isabelle
    ,".ToHaskellAS", ".StructureAna", ".OWLAnalysis" -- OWL_DL
    , ".Haskell2DG", ".CreateModules"  -- Haskell
    , "Comorphisms.KnownProvers", "GUI.GenericATPState", "PGIP.Utils"
    , "GUI.Utils", "GUI.ProofManagement" -- Proofs 
    , "Proofs.Automatic", "Driver.Options" -- Static
    , "Proofs.EdgeUtils", "Proofs.StatusUtils" -- Driver
    , "SPASS.Utils", "Proofs.BatchProcessing", "GUI.GenericATPState"
    , "GUI.GenericATP", "SPASS.CreateDFGDoc" -- SPASS
 --   , "GUI.Taxonomy", "GUI.ShowGraph" -- PGIP
    , "Static.DevGraph", "Syntax.AS_Library", "Static.AnalysisLibrary"
    , "OMDoc.HetsInterface", "OMDoc.OMDocOutput" -- OMDOC
    ] 

getContent2 :: String -> [String] -> [(String, String)]
getContent2 x  = map (\ m -> (x, m)) 

getContent4 :: [String] -> [String]
getContent4 s = map ((!! 1) .  words) s

getContent5 :: [String] -> [String]
getContent5  = map $ fst . break (== '(') 

getContent6 :: [[String]] ->[[String]]
getContent6 = map $ (filter (elem '.')) . getContent5 . getContent4

isIn3 :: (Eq a)=> [(a, a)] -> [(a, a)]
isIn3 = filter (\(x,y) -> x /= y) 
