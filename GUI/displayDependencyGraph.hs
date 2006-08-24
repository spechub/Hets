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
import Events
import Destructible

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel

import System.Directory
import Data.List
import Text.ParserCombinators.Parsec


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
    let subNodeMenu = LocalMenu (Menu Nothing [])
        subNodeTypeParms =
                         subNodeMenu $$$
                         Ellipse $$$
                         ValueTitle id $$$
                         Color "yellow" $$$
                         emptyNodeTypeParms
    subNodeType <- newNodeType depG subNodeTypeParms
    subNodeList <- mapM (newNode depG subNodeType . return) fln
    let subArcMenu = LocalMenu( Menu Nothing [])
        subArcTypeParms = subArcMenu $$$
                          ValueTitle id $$$
                          Color "green" $$$
                          emptyArcTypeParms
    subArcType <- newArcType depG subArcTypeParms
    redraw depG
    sync(destroyed depG)
    -- putStrLn $ show $ zip fln sss

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
