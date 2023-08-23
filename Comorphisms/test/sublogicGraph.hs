{- |
Module      :  ./Comorphisms/test/sublogicGraph.hs
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (via imports)

-}

module Main where

import Comorphisms.HetLogicGraph
import Comorphisms.LogicGraph

import Logic.Comorphism
import Logic.Logic

import Data.Maybe
import qualified Data.Map as Map

import Control.Monad (unless)
import System.Exit (exitFailure)

main :: IO ()
main = do
  testSuccess <- testInj_mapSublogicAll
  hsg <- hetSublogicGraph
  putStrLn ("Size of HetSublogicGraph (n,e): " ++ show (size hsg))
  unless testSuccess exitFailure

size :: HetSublogicGraph -> (Int, Int)
size hsg = (Map.size $ sublogicNodes hsg,
            Map.fold (\ x y -> length x + y) 0 $ comorphismEdges hsg)

testInj_mapSublogic :: (Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2)
                   => cid -> Bool
testInj_mapSublogic cid =
        all (isJust . parseSublogic (targetLogic cid) . sublogicName)
        $ mapMaybe (mapSublogic cid) $ all_sublogics $ sourceLogic cid

testInj_mapSublogicAll :: IO Bool
testInj_mapSublogicAll = do
  putStrLn "Every Comorphism should be followed by True"
  let testResults = map (\ (Comorphism c) -> testInj_mapSublogic c)
                          comorphismList
  mapM_ showTest $ zip comorphismList testResults
  putStrLn ("Test " ++ if and testResults then "succeeded." else "failed!")
  return (and testResults)
    where showTest (acm, res) = putStrLn (show acm ++ " : " ++ show res)
