{- |
Module      :  $Header$
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

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe

import Common.Consistency
import Common.ToXml

import Text.XML.Light

lGToXml :: LogicGraph -> Element
lGToXml lg = let
  cs = Map.elems $ comorphisms lg
  ssubs = Set.toList . Set.fromList
    $ map (\ (Comorphism cid) -> G_sublogics (sourceLogic cid)
           $ sourceSublogic cid) cs
  tsubs = Set.toList . Set.fromList
    $ map (\ (Comorphism cid) -> G_sublogics (targetLogic cid)
           $ targetSublogic cid) cs
  in unode "LogicGraph"
  $ map logicToXml (Map.elems $ logics lg)
  ++ map (\ a -> add_attr (mkNameAttr $ show a) $ unode "sourceSublogic" ())
    ssubs
  ++ map (\ a -> add_attr (mkNameAttr $ show a) $ unode "targetSublogic" ())
    tsubs
  ++ map comorphismToXml cs

logicToXml :: AnyLogic -> Element
logicToXml (Logic lid) = add_attrs
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
  ++ map (\ a -> add_attr (mkNameAttr $ proverName a) $ unode "Prover" ())
            (provers lid)
  ++ map (\ a -> add_attr (mkNameAttr $ ccName a)
          $ unode "ConsistencyChecker" ()) (cons_checkers lid)
  ++ map (\ a -> add_attr (mkNameAttr $ checkerId a)
          $ unode "ConservativityChecker" ()) (conservativityCheck lid)

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
