{- |
Module      :  $Header$
Description :  hets server queries
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}

module PGIP.Query where

{-

As a path we expect an existing directory, a file or library name or a
number (Int) referecing a current LibEnv (or Session). The session also stores
the top-level library name.

In order to address other (i.e. imported) libraries of a session given by a
number this number should be part of a query containing "dg=<id>" with the
library name as path.

As queries we basically allow actions to be taken, like displaying:
 - the whole LibEnv
 - the development graph (for a library name)
    - as xml or svg
 - a specific node or edge from a development graph (given by id=<id>)
    in various format (like local or global theory)
other actions are commands like performing global decomposition (or "auto")
on a graph or individual proofs on a node or edge.

But rather than requiring a full query like "?dg=5&command=display&format=xml"
it should be sufficient to write "/5?xml" or "/5?auto". The notation "dg=5" is
only necessary to address an imported library of the session. Also some
default display should be generated for a missing query like just "/5".

State changing commands like "auto" (or other proofs) will generate a new
numbers for the new graphs (i.e. "dg=6").

The default display for a LibEnv should be:

 - the current top-level library name
 - links to every imported library
 - links to display the current top-level development graphs in various formats.
 - links to perform the possible global commands
 - (several) links for every node
 - (several) links for every edge

-}

import Common.LibName
import Common.Utils

import Interfaces.Command
import Interfaces.CmdAction

import Static.DevGraph

import Data.Char
import Data.List
import Data.Maybe

displayTypes :: [String]
displayTypes = ["svg", "xml", "dot", "session"]

nodeCommands :: [String]
nodeCommands = ["node", "theory", "provers", "translations", "prove"]

proveParams :: [String]
proveParams = ["include", "prover", "translation"]

edgeCommands :: [String]
edgeCommands = ["edge"]

getGlobCmds :: [(GlobCmd, a)] -> [String]
getGlobCmds = map (cmdlGlobCmd . fst)

globalCommands :: [String]
globalCommands = concat
  [ getGlobCmds globLibAct
  , getGlobCmds globLibResultAct
  , getGlobCmds globResultAct ]

data DGQuery = DGQuery
  { queryId :: Int
  , optQueryLibPath :: Maybe PATH
  }
  | NewDGQuery { queryLib :: FilePath }

data Query = Query
  { dgQuery :: DGQuery
  , queryKind :: QueryKind
  }

data QueryKind =
    DisplayQuery (Maybe String)
  | GlobCmdQuery String
  | NodeQuery Int NodeCommand
  | EdgeQuery EdgeId String


data NodeCommand =
    NcTheory
  | NcInfo
  | NcProvers (Maybe String)
  | NcTranslations (Maybe String)
  | ProveNode
  { ncInclTheorems :: Bool
  , ncProver :: Maybe String
  , ncTranslation :: Maybe String }
  deriving Show

-- | the path is not empty and leading slashes are removed
anaUri :: FilePath -> String -> Either String Query
anaUri path query = case anaQuery query of
    Right (mi, qk) -> case (mi, readMaybe path) of
      (Just i, Just j) | i /= j -> Left "different dg ids"
      (_, mj) -> Right $ Query
        (case catMaybes [mi, mj] of
          [] -> NewDGQuery path
          i : _ -> DGQuery i $ if isJust mj then Nothing else Just path)
        qk
    Left err -> Left err

-- | a leading question mark is removed
anaQuery :: String -> Either String (Maybe Int, QueryKind)
anaQuery qstr =
       let globals = "update" : globalCommands
           q = map (splitOn '=') $ concatMap (splitOn ';') $ splitOn '&' qstr
           isNat s = all isDigit s && length s < 11
           (q1, qm) = partition (\ l -> case l of
                        [x] -> isNat x || elem x
                               (displayTypes ++ globals ++ ["include"]
                                ++ nodeCommands ++ edgeCommands)
                        _ -> False) q
           (q2, qr) = partition (\ l -> case l of
                        [x, y] -> elem x (["dg", "id", "session"]
                                          ++ nodeCommands ++ edgeCommands)
                                   && isNat y
                                  || x == "command" &&
                                     elem y globals
                                  || x == "format" && elem y displayTypes
                                  || elem x proveParams
                        _ -> False) qm
           (fs, r1) = partition (`elem` displayTypes) $ map head q1
           (gs, r2) = partition (`elem` globals) r1
           (ns, r3) = partition (`elem` nodeCommands) r2
           (es, r4) = partition (`elem` edgeCommands) r3
           (incls, is) = partition (== "include") r4
           (fs2, p1) = partition ((== "format") . head) q2
           (cs2, p2) = partition ((== "command") . head) p1
           (is2, p3) = partition ((`elem` ["dg", "session"]) . head) p2
           (ns2, p4) = partition ((`elem` nodeCommands) . head) p3
           (es2, p5) = partition ((`elem` edgeCommands) . head) p4
           (pps, ids) = partition ((`elem` proveParams) . head) p5
           snds = map $ head . tail
           afs = nubOrd $ fs ++ snds fs2
           ags = nubOrd $ gs ++ snds cs2
           ans = nubOrd $ ns ++ map head ns2
           aes = nubOrd $ es ++ map head es2
           ais = nubOrd $ is ++ snds is2
           aids = nubOrd . snds $ ns2 ++ es2 ++ ids
           mi = fmap read $ listToMaybe ais
           noPP = null pps && null incls
       in if null qr && length ais < 2 then case (afs, ags, ans, aes, aids) of
         (_, [], [], [], []) | noPP -> if length afs > 1
           then Left $ "non-unique format " ++ show afs
           else Right (mi, DisplayQuery $ listToMaybe afs)
         (_, c : r, [], [], _) | noPP -> if null r
           then Right (mi, GlobCmdQuery c)
           else Left $ "non-unique command " ++ show r
         (_, [], _, [], i : s) ->
           anaNodeQuery mi ans (read i) s incls pps
         (_, [], [], e : r, i : s) | noPP -> if null r && null s then
           Right (mi, EdgeQuery (EdgeId $ read i) e)
           else Left $ "non-unique edge " ++ show (aes ++ aids)
         _ -> Left $ "non-unique query " ++ show q
       else Left $ if null qr then "non-unique dg " ++ show q else
                       "ill-formed query " ++ show qr

anaNodeQuery :: Maybe Int -> [String] -> Int -> [String] -> [String]
  -> [[String]] -> Either String (Maybe Int, QueryKind)
anaNodeQuery mi ans i s incls pss =
  let pps = foldr (\ l -> case l of
                [x, y] -> ((x, y) :)
                _ -> id) [] pss
      pp = anaProveParams incls pps
      noPP = null incls && null pps
  in if null s then case ans of
       [] -> Right (mi, NodeQuery i
         $ if noPP then NcInfo else pp)
       [cmd] -> case cmd of
         "prove" -> Right (mi, NodeQuery i pp)
         "node" | noPP -> Right (mi, NodeQuery i NcInfo)
         "theory" | noPP -> Right (mi, NodeQuery i NcTheory)
         "provers" | null incls ->
            Right (mi, NodeQuery i $ NcProvers (lookup "translation" pps))
         "translations" | null incls ->
            Right (mi, NodeQuery i $ NcTranslations (lookup "prover" pps))
         _ -> Left $ "unknown node command '" ++ cmd ++ "' "
              ++ show (incls : pss)
       _ -> Left $ "non-unique node command " ++ show ans
  else Left $ "non-unique node ids " ++ show (show i : s)

anaProveParams :: [String] -> [(String, String)] -> NodeCommand
anaProveParams incls pps =
  ProveNode (not (null incls) || case lookup "include" pps of
    Nothing -> True
    Just str -> notElem (map toLower str) ["f", "false"])
    (lookup "prover" pps)
    (lookup "translation" pps)
