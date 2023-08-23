{- |
Module      :  ./Logic/LGToXml.hs
Description :  export logic graph information as XML
Copyright   :  (c) Christian Maeder DFKI GmbH 2013
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

export logic graph information as XML
-}

module Logic.LGToXml where

import Logic.Comorphism
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover

import Control.Monad

import qualified Data.Map as Map
import Data.Char
import Data.Maybe

import Common.Consistency
import Common.ToXml

import Text.XML.Light

usableProvers :: LogicGraph -> IO Element
usableProvers lg = do
  ps <- mapM proversOfLogic . Map.elems $ logics lg
  return $ unode "provers" $ concat ps

proversOfLogic :: AnyLogic -> IO [Element]
proversOfLogic (Logic lid) = do
  bps <- filterM (fmap isNothing . proverUsable) $ provers lid
  return $ map (\ p ->
      add_attrs [ mkNameAttr $ proverName p
                , mkAttr "logic" $ language_name lid]
      $ unode "prover" ()) bps

lGToXml :: LogicGraph -> IO Element
lGToXml lg = do
  let cs = Map.elems $ comorphisms lg
      groupC = Map.toList . Map.fromListWith (++)
      ssubs = groupC
        $ map (\ (Comorphism cid) -> (G_sublogics (sourceLogic cid)
           $ sourceSublogic cid, [language_name cid])) cs
      tsubs = groupC
        $ map (\ (Comorphism cid) -> (G_sublogics (targetLogic cid)
           $ targetSublogic cid, [language_name cid])) cs
      nameC = map (\ n -> add_attr (mkNameAttr n) $ unode "comorphism" ())
  ls <- mapM logicToXml . Map.elems $ logics lg
  return $ unode "LogicGraph"
    $ ls
    ++ map (\ (a, ns) -> add_attr (mkNameAttr $ show a)
          $ unode "sourceSublogic" $ nameC ns) ssubs
    ++ map (\ (a, ns) -> add_attr (mkNameAttr $ show a)
          $ unode "targetSublogic" $ nameC ns) tsubs
    ++ map comorphismToXml cs

logicToXml :: AnyLogic -> IO Element
logicToXml (Logic lid) = do
 let ps = provers lid
     cs1 = cons_checkers lid
     cs2 = conservativityCheck lid
     ua b = mkAttr "usable" . map toLower $ show $ isNothing b
 bps <- mapM proverUsable ps
 bcs1 <- mapM ccUsable cs1
 bcs2 <- mapM checkerUsable cs2
 return $ add_attrs
  [ mkNameAttr $ language_name lid
  , mkAttr "Stability" . show $ stability lid
  , mkAttr "has_basic_parser" . show . not . Map.null $ parsersAndPrinters lid
  , mkAttr "has_basic_analysis" . show . isJust $ basic_analysis lid
  , mkAttr "has_symbol_list_parser" . show . isJust $ parse_symb_items lid
  , mkAttr "has_symbol_map_parser" . show . isJust $ parse_symb_map_items lid
  , mkAttr "is_a_process_logic" . show . isJust $ data_logic lid
  ] . unode "logic"
  $ unode "Description" (mkText $ description lid)
  : map (\ a -> add_attr (mkNameAttr a) $ unode "Serialization" ())
    (filter (not . null) . Map.keys $ parsersAndPrinters lid)
  ++ zipWith (\ a b -> add_attrs [mkNameAttr $ proverName a, ua b]
              $ unode "Prover" ()) ps bps
  ++ zipWith (\ a b -> add_attrs [mkNameAttr $ ccName a, ua b]
              $ unode "ConsistencyChecker" ()) cs1 bcs1
  ++ zipWith (\ a b -> add_attrs [mkNameAttr $ checkerId a, ua b]
              $ unode "ConservativityChecker" ()) cs2 bcs2
  ++ [unode "Sublogics" . unlines . map sublogicName $ all_sublogics lid]

comorphismToXml :: AnyComorphism -> Element
comorphismToXml (Comorphism cid) = add_attrs
  [ mkNameAttr $ language_name cid
  , mkAttr "source" $ language_name (sourceLogic cid)
  , mkAttr "target" $ language_name (targetLogic cid)
  , mkAttr "sourceSublogic" . sublogicName $ sourceSublogic cid
  , mkAttr "targetSublogic" . sublogicName $ targetSublogic cid
  , mkAttr "is_inclusion" . show $ isInclusionComorphism cid
  , mkAttr "has_model_expansion" . show $ has_model_expansion cid
  , mkAttr "is_weakly_amalgamable" . show $ is_weakly_amalgamable cid
  ] $ unode "comorphism" ()
