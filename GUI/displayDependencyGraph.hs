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
        fln' = nub fln
    lfs <- mapM (readFile . (++ ".imports")) ffnn
    let ss = map (filter (isPrefixOf "import") . lines) lfs
        sss = getContent6 ss
        ssss' = map (filter ( \ s -> all (not . (`isSublistOf` s)) excludes))
                    sss 
        ssss = map (map $ fst . break (== '.')) ssss'
        sss' = map nub ssss
        graphParms = GraphTitle "Dependency Graph" $$
                        OptimiseLayout True $$
                        AllowClose (return True) $$
                        emptyGraphParms
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
                     $ isIn3 $ concat $ zipWith getContent2 ffnn sss'
    redraw depG
    sync(destroyed depG)

excludes = ["ATC", ".Logic_"]

getContent2 :: String -> [String] -> [(String, String)]
getContent2 x l = if any (`isSublistOf` x) excludes then []
                 else map (\ m -> (fst $ break (== '.') x, m)) l

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


isIn3 :: (Eq a)=> [(a, a)] -> [(a, a)]
isIn3 = filter (\(x,y) -> x /= y) 

isSublistOf :: (Eq a) => [a] -> [a] -> Bool
isSublistOf [] _ = True
isSublistOf _ [] = False
isSublistOf ys l@(_:l')
    | length ys <= length l = (ys `isPrefixOf` l) || (ys `isSublistOf` l')
    | otherwise = False