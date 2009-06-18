{- |
Module      :  $Header$
Description :  Functions for selective debugging
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

specialized debugging functions
-}

module OMDoc.KeyDebug where

import qualified Data.Map as Map
import System.IO (putStrLn)
import Debug.Trace (trace)
import Data.Char (toLower)
import Data.List (find, isPrefixOf, isInfixOf, intercalate)
import Common.Utils (getEnvDef, splitOn, trim)
import qualified System.IO.Unsafe as SysUnsafe

type DbgKey = String

data DbgKeyPolicy = KPExact | KPPrefix | KPContains
        deriving (Eq, Ord)

instance Show DbgKeyPolicy where
        show KPExact = "exact"
        show KPPrefix = "prefix"
        show KPContains = "contains"

stringToPolicy::String->Maybe DbgKeyPolicy
stringToPolicy = _stringToPolicy . (map toLower)
        where
        _stringToPolicy::String->Maybe DbgKeyPolicy
        _stringToPolicy ('e':_) = Just KPExact
        _stringToPolicy ('p':_) = Just KPPrefix
        _stringToPolicy ('c':_) = Just KPContains
        _stringToPolicy _ = Nothing

keysWithPolicy::DbgKeyPolicy->[DbgKey]->Map.Map DbgKeyPolicy [DbgKey]
keysWithPolicy _ [] = Map.empty
keysWithPolicy p keys = Map.singleton p keys

processDbgKeys::String->(Map.Map DbgKeyPolicy [DbgKey], Map.Map DbgKeyPolicy [DbgKey])
processDbgKeys s =
        let
                pkeys = map trim $ splitOn ',' s
                (enkeys, diskeys) = foldl (\(e,d) i -> if head i == '!' then (e,d++[drop 1 i]) else (e++[i],d)) ([],[]) pkeys
                [enpolsep, dispolsep] = map (map (splitOn ':')) [enkeys, diskeys]
                ekwp = map (\ps ->
                        case ps of
                                [] -> error "error in processDbgKeys..."
                                [justakey] -> (KPExact, justakey)
                                (p:ks) -> case stringToPolicy p of
                                        Just policy -> (policy, intercalate ":" ks)
                                        Nothing -> (KPExact, intercalate ":" (p:ks))
                                        ) enpolsep
                dkwp = map (\ps ->
                        case ps of
                                [] -> error "error in processDbgKeys..."
                                [justakey] -> (KPExact, justakey)
                                (p:ks) -> case stringToPolicy p of
                                        Just policy -> (policy, intercalate ":" ks)
                                        Nothing -> (KPExact, intercalate ":" (p:ks))
                                        ) dispolsep
                [ekmap, dkmap] = map (foldl (\m (p,k) ->
                        Map.insert p ((Map.findWithDefault [] p m) ++ [k]) m
                        ) Map.empty) [ekwp, dkwp]
        in
                (ekmap, dkmap)

data DbgInf =
        DbgInf
                {
                          dbgKeys::Map.Map DbgKeyPolicy [DbgKey]
                        , dbgDisKeys :: Map.Map DbgKeyPolicy [DbgKey]
                }
                deriving Show

emptyDbgInf::DbgInf
emptyDbgInf = DbgInf { dbgKeys = Map.empty, dbgDisKeys = Map.empty }

simpleDebug::[DbgKey]->DbgInf
simpleDebug keys = emptyDbgInf { dbgKeys = keysWithPolicy KPExact keys }

mkDebug::[DbgKey]->[DbgKey]->DbgInf
mkDebug keys diskeys = emptyDbgInf { dbgKeys = keysWithPolicy KPExact keys, dbgDisKeys = keysWithPolicy KPExact diskeys }

mkDebugExt::[DbgKey]->[DbgKey]->DbgKeyPolicy->DbgKeyPolicy->DbgInf
mkDebugExt keys diskeys ep dp =
        emptyDbgInf { dbgKeys = keysWithPolicy ep keys, dbgDisKeys = keysWithPolicy dp diskeys }

mkDebugKeys::String->DbgInf
mkDebugKeys s =
        let
                (enmap, dismap) = processDbgKeys s
        in
                emptyDbgInf { dbgKeys = enmap, dbgDisKeys = dismap }

addDbgKey::DbgInf->DbgKey->DbgInf
addDbgKey dbginf key = dbginf { dbgKeys = Map.insertWith (++) KPExact [key] (dbgKeys dbginf) }

addDbgDisKey::DbgInf->DbgKey->DbgInf
addDbgDisKey dbginf key = dbginf { dbgDisKeys = Map.insertWith (++) KPExact [key] (dbgDisKeys dbginf) }

mergeDbgInf::DbgInf->DbgInf->DbgInf
mergeDbgInf di1 di2 =
        di1 {
                 dbgKeys = Map.unionWith (++) (dbgKeys di1) (dbgKeys di2)
                ,dbgDisKeys = Map.unionWith (++) (dbgDisKeys di1) (dbgDisKeys di2)
                }

policyElem::DbgKeyPolicy->[DbgKey]->DbgKey->Bool
policyElem KPExact kl k = elem k kl
policyElem KPPrefix kl k =
        case (find (\key -> isPrefixOf key k) kl) of
                Nothing -> False
                _ -> True
policyElem KPContains kl k =
        case (find (\key -> isInfixOf key k) kl) of
                Nothing -> False
                _ -> True

isDisabledKey::DbgInf->DbgKey->Bool
isDisabledKey dbginf key =
        any (\p -> policyElem p (Map.findWithDefault [] p (dbgDisKeys dbginf)) key) (Map.keys (dbgDisKeys dbginf))

isEnabledKey::DbgInf->DbgKey->Bool
isEnabledKey dbginf key =
        if isDisabledKey dbginf key
                then
                        False
                else
                        (elem "all" (Map.findWithDefault [] KPExact (dbgKeys dbginf)))
                        || any (\p -> policyElem p (Map.findWithDefault [] p (dbgKeys dbginf)) key) (Map.keys (dbgKeys dbginf))


envDebug::IO DbgInf
envDebug =
  do
    envdbg <- getEnvDef "OMDOC_DEBUG" ""
    return $
      case trim $ envdbg of
        [] -> emptyDbgInf
        _ -> mkDebugKeys envdbg

debug::forall a . DbgInf->DbgKey->String->a->a
debug dbginf dbgkey msg x =
  let
    envDbgInf = SysUnsafe.unsafePerformIO envDebug
  in
    if (isEnabledKey dbginf dbgkey) || (isEnabledKey envDbgInf dbgkey)
      then
        Debug.Trace.trace (dbgkey ++ ": " ++ msg) x
      else
        x

debugIO::DbgInf->DbgKey->String->IO ()
debugIO dbginf dbgkey msg =
  do
    envDbgInf <- envDebug
    if (isEnabledKey dbginf dbgkey) || (isEnabledKey envDbgInf dbgkey)
      then
        putStrLn (dbgkey ++ ": " ++ msg)
      else
        return ()

debugEnv::forall a . DbgKey->String->a->a
debugEnv = debug emptyDbgInf
