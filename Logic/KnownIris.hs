{- |
Module      :  ./Logic/KnownIris.hs
Description :  map of the known logics and serializations
Copyright   :  (c) Soeren Schulze, Uni Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Logic.KnownIris where

import qualified Data.Map as Map

logPrefix, serPrefix :: String

logPrefix = "http://purl.net/DOL/logics/"
serPrefix = "http://purl.net/DOL/serializations/"
lngPrefix = "http://purl.net/DOL/languages/"
trlPrefix = "http://purl.net/DOL/translations/"

logicNames :: Map.Map String String
logicNames = -- IRI -> local name
  Map.fromList
  [ (logPrefix ++ "CommonLogic", "CommonLogic"),
    -- TODO: Properly support `language` declarations
    -- Everything up to the `logPrefix` lines below is part of a hack to
    -- support `translation` declarations and `language` declarations without
    -- an accompanying `logic` declaration by essentially treating `language`
    -- the same as `logic`.
    -- This should probably be done properly instead, but it works for now.
    (lngPrefix ++ "CASL", "CASL"),
    (lngPrefix ++ "CommonLogic", "CommonLogic"),
    (lngPrefix ++ "HasCASL", "HasCASL"),
    (lngPrefix ++ "Propositional", "Propositional"),
    (lngPrefix ++ "OWL", "OWL"),
    (lngPrefix ++ "OWL2", "OWL"),
    (trlPrefix ++ "SROIQtoCL", "OWL22CommonLogic"),
    (trlPrefix ++ "PropositionalToSROIQ", "Propositional2OWL2"),
    (logPrefix ++ "Propositional", "Propositional"),
    (logPrefix ++ "OWL2", "OWL"),
    (logPrefix ++ "SROIQ", "OWL")] -- should be "NP-sROIQ-D|-|"
                                   -- (or "OWL.NP-sROIQ-D|-|"?) instead of
                                   -- "OWL" but Hets claims not to kow both.

lookupLogicName :: String -> Maybe String
lookupLogicName = (`Map.lookup` logicNames) . filter (not . (`elem` "<>"))

serializations :: String -> Map.Map String String
serializations l
  | l == "CommonLogic" =
    Map.fromList [ (serPrefix ++ "CommonLogic/CLIF", "CLIF"),
                   (serPrefix ++ "CommonLogic/KIF", "KIF") ]
  | l == "Propositional" =
    Map.fromList [ (serPrefix ++ "Propositional/Hets", "Hets") ]
  | l == "OWL" =
    Map.fromList [ (serPrefix ++ "OWL2/Manchester", "Manchester") ]
  | otherwise = Map.empty

lookupSerialization :: String -> String -> Maybe String
lookupSerialization l = (`Map.lookup` serializations l) .
                        filter (not . (`elem` "<>"))
