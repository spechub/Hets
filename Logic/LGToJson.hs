{- |
Module      :  ./Logic/LGToJson.hs
Description :  export logic graph information as Json
Copyright   :  (c) Christian Maeder DFKI GmbH 2013
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

export logic graph information as Json
-}

module Logic.LGToJson where

import Logic.Comorphism
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover

import Control.Monad

import qualified Data.Map as Map
import Data.Maybe

import Common.Consistency
import Common.Json

usableProvers :: LogicGraph -> IO Json
usableProvers lg = do
  ps <- mapM proversOfLogic . Map.elems $ logics lg
  return $ mkJObj [("provers", mkJArr $ concat ps)]

proversOfLogic :: AnyLogic -> IO [Json]
proversOfLogic (Logic lid) = do
  bps <- filterM (fmap isNothing . proverUsable) $ provers lid
  return $ map (\ p ->
      mkJObj [ mkNameJPair $ proverName p
             , mkJPair "logic" $ language_name lid ]) bps

lGToJson :: LogicGraph -> IO Json
lGToJson lg = do
  let cs = Map.elems $ comorphisms lg
      groupC = Map.toList . Map.fromListWith (++)
      ssubs = groupC
        $ map (\ (Comorphism cid) -> (G_sublogics (sourceLogic cid)
           $ sourceSublogic cid, [language_name cid])) cs
      tsubs = groupC
        $ map (\ (Comorphism cid) -> (G_sublogics (targetLogic cid)
           $ targetSublogic cid, [language_name cid])) cs
  ls <- mapM logicToJson . Map.elems $ logics lg
  return $ mkJObj [("logic_graph", mkJObj
    [ ("logics", mkJArr ls)
    , ("source_sublogics", mkJArr $ map (\ (a, ns) -> mkJObj
             [ mkNameJPair $ show a
             , ("comorphisms", mkJArr $ map mkJStr ns)]) ssubs)
    , ("target_sublogics", mkJArr $ map (\ (a, ns) -> mkJObj
             [ mkNameJPair $ show a
             , ("comorphisms", mkJArr $ map mkJStr ns)]) tsubs)
    , ("comorphisms", mkJArr $ map comorphismToJson cs)] )]

logicToJson :: AnyLogic -> IO Json
logicToJson (Logic lid) = do
 let ps = provers lid
     cs1 = cons_checkers lid
     cs2 = conservativityCheck lid
     ua b = ("usable", mkJBool $ isNothing b)
 bps <- mapM proverUsable ps
 bcs1 <- mapM ccUsable cs1
 bcs2 <- mapM checkerUsable cs2
 return $ mkJObj
  [ mkNameJPair $ language_name lid
  , mkJPair "Stability" . show $ stability lid
  , ("has_basic_parser", mkJBool . not . Map.null $ parsersAndPrinters lid)
  , ("has_basic_analysis", mkJBool . isJust $ basic_analysis lid)
  , ("has_symbol_list_parser", mkJBool . isJust $ parse_symb_items lid)
  , ("has_symbol_map_parser", mkJBool . isJust $ parse_symb_map_items lid)
  , ("is_a_process_logic", mkJBool . isJust $ data_logic lid)
  , ("description_lines", mkJArr . map mkJStr . lines $ description lid)
  , ("serializations", mkJArr . map mkJStr
     . filter (not . null) . Map.keys $ parsersAndPrinters lid)
  , ("provers", mkJArr $ zipWith (\ a b ->
         mkJObj [mkNameJPair $ proverName a, ua b]) ps bps)
  , ("consistency_checkers", mkJArr $ zipWith (\ a b ->
         mkJObj [mkNameJPair $ ccName a, ua b]) cs1 bcs1)
  , ("conservativity_checkers", mkJArr $ zipWith (\ a b ->
          mkJObj [mkNameJPair $ checkerId a, ua b]) cs2 bcs2)
  , ("sublogics", mkJArr . map (mkJStr . sublogicName) $ all_sublogics lid)]

comorphismToJson :: AnyComorphism -> Json
comorphismToJson (Comorphism cid) = mkJObj
  [ mkNameJPair $ language_name cid
  , mkJPair "source" $ language_name (sourceLogic cid)
  , mkJPair "target" $ language_name (targetLogic cid)
  , mkJPair "sourceSublogic" . sublogicName $ sourceSublogic cid
  , mkJPair "targetSublogic" . sublogicName $ targetSublogic cid
  , ("is_inclusion", mkJBool $ isInclusionComorphism cid)
  , ("has_model_expansion", mkJBool $ has_model_expansion cid)
  , ("is_weakly_amalgamable", mkJBool $ is_weakly_amalgamable cid)
  ]
