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
        fln = map (deletWith init 8) fn 
    lfs <- mapM (readFile) fn
    let ss = map (filter (isPrefixOf "import") . lines) lfs
        sss = getContent6 ss 
        graphParms = GraphTitle "Dependency Graph" $$
                        OptimiseLayout True $$
                        AllowClose (return True) $$
                        emptyGraphParms
    depG <- newGraph daVinciSort graphParms
    let flln = fln ++ (isIn2 [] $ concat $ isIn fln sss)
        subNodeMenu = LocalMenu (Menu Nothing [])
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
                     $ getContent1 $ zipWith getContent2 fln sss
    redraw depG
    sync(destroyed depG)


getContent1 :: [[(String,String)]] -> [(String,String)]
getContent1 [] = []
getContent1 (x:xs) = x ++ getContent1 xs

getContent2 :: String -> [String] -> [(String,String)]
getContent2 _ [] =[]
getContent2 s (x:xs) = (s,x):getContent2 s xs

getContent3 :: String -> String
getContent3 [] = ""
getContent3 (x:xs) = if x == '(' then ""
                      else x : getContent3 xs

getContent4 :: [String] -> [String]
getContent4 s = map (!! 1) $  map  words s

getContent5 :: [String] -> [String]
getContent5  = map  getContent3 

getContent6 :: [[String]] ->[[String]]
getContent6 = map (getContent5 . getContent4)

deletWith :: (String -> String) -> Int -> String -> String
deletWith f n s = case n of
    0 -> s
    _ -> deletWith f (n-1) $ f s

isIn :: [String] -> [[String]] -> [[String]]
isIn l ll = map (is l) ll

is :: [String] -> [String] -> [String]
is [] l = l
is _ [] = []
is l' (x:xs) | elem x l' = is l' xs
             | otherwise = x : is l' xs

isIn2 :: [String] -> [String] -> [String]
isIn2 l []  = l
isIn2 l (x:xs) | elem x l = isIn2 l xs
               | otherwise = isIn2 (l ++ [x]) xs 
