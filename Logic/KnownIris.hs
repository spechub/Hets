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

import qualified Data.HashMap.Lazy as Map

logPrefix, serPrefix :: String

logPrefix = "http://purl.net/dol/logics/"
serPrefix = "http://purl.net/dol/serializations/"

logicNames :: Map.HashMap String String
logicNames = -- IRI -> local name
  Map.fromList
  [ (logPrefix ++ "CommonLogic", "CommonLogic"),
    (logPrefix ++ "Propositional", "Propositional"),
    (logPrefix ++ "OWL2", "OWL") ]

lookupLogicName :: String -> Maybe String
lookupLogicName = (`Map.lookup` logicNames)

serializations :: String -> Map.HashMap String String
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
lookupSerialization l = (`Map.lookup` serializations l)
