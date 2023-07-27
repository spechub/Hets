{- |
Module      :  ./Logic/PrintLogics.hs
Description :  Print list of all logics
Copyright   :  (c) Till Mossakowski, and OvGU Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@iks.cs.ovgu.de
Stability   :  provisional
Portability :  non-portable (various -fglasgow-exts extensions)

Print list of all logics with some useful information.

-}

module Logic.PrintLogics where

import Comorphisms.LogicList
import Logic.Prover
import Logic.Logic
import Control.Monad
import Data.List

printLogics :: IO ()
printLogics = do
  putStrLn "*** List of logics in Hets ***"
  mapM_ printLogicsWithStability [Stable, Testing, Experimental, Unstable]

hasStability :: Stability -> AnyLogic -> Bool
hasStability s (Logic l) = stability l == s

printLogicsWithStability :: Stability -> IO ()
printLogicsWithStability s = do
  putStrLn $ "Stability: "++show s
  mapM_ printLogic $ filter (hasStability s) logicList
  
printLogic :: AnyLogic -> IO ()
printLogic (Logic l) = do
  putStrLn $ "  "++show l++": "++short_description l
  let ps = provers l
  unless (null ps) $ do
    putStr "    provers: "
    putStrLn $ intercalate ", " $ map proverName ps

