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
import Events
import Destructible

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel

import System.Directory
import Data.List

main :: IO ()
main = do
    fs <- getDirectoryContents "."
    let fn = filter (isSuffixOf ".imports") fs
        ffn = map (deletWith init 8) fn
        ffnn = filter (elem '.') ffn
        fln = map (fst . break (== '.'))  ffnn 
        fln' = isIn2 [] fln
    lfs <- mapM (readFile . (++ ".imports")) ffnn
    let ss = map (filter (isPrefixOf "import") . lines) lfs
        sss = getContent6 ss
        ssss = map (map $ fst . break (== '.')) sss
        sss' = map (isIn2 []) ssss
        graphParms = GraphTitle "Dependency Graph" $$
                        OptimiseLayout True $$
                        AllowClose (return True) $$
                        emptyGraphParms
    depG <- newGraph daVinciSort graphParms
    let flln = isIn2 [] $ fln' ++ concat sss'
        subNodeMenu = LocalMenu (Menu (Just "Info") [])
        subNodeTypeParms =
                         subNodeMenu $$$
                         Ellipse $$$
                         ValueTitle id $$$
                         Color "yellow" $$$
                         emptyNodeTypeParms
    subNodeType <- newNodeType depG subNodeTypeParms
    subNodeList <- mapM (newNode depG subNodeType . return) flln
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
                     Rel.toList $ Rel.intransKernel $ Rel.fromList
                     $ isIn3 $ isIn2 [] $ concat $ zipWith getContent2 fln sss'
    redraw depG
    sync(destroyed depG)

getContent2 :: a -> [b] -> [(a, b)]
getContent2 x  = map (\ m -> (x, m))

getContent4 :: [String] -> [String]
getContent4 s = map ((!! 1) .  words) s

getContent5 :: [String] -> [String]
getContent5  = map $ fst . break (== '(') 

getContent6 :: [[String]] ->[[String]]
getContent6 = map $ (filter (elem '.')) . getContent5 . getContent4

deletWith :: ([a] -> [a]) -> Int -> [a] -> [a]
deletWith f n s = case n of
    0 -> s
    _ -> deletWith f (n-1) $ f s

isIn2 :: (Eq a)=> [a] -> [a] -> [a]
isIn2 l []  = l
isIn2 l (x:xs) | elem x l = isIn2 l xs
               | otherwise = isIn2 (l ++ [x]) xs 

isIn3 :: (Eq a)=> [(a, a)] -> [(a, a)]
isIn3 [] = []
isIn3 ((m, n):xs) | m == n = isIn3 xs
                    | otherwise = (m, n) : isIn3 xs