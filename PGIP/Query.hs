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
nodeCommands = ["node", "theory"]

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
  | NodeQuery Int (Maybe String)
  | EdgeQuery EdgeId String

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

-- we have a library name

-- | a leading question mark is removed
anaQuery :: String -> Either String (Maybe Int, QueryKind)
anaQuery qstr =
       let q = map (splitOn '=') $ concatMap (splitOn ';') $ splitOn '&' qstr
           isNat s = all isDigit s && length s < 11
           (q1, qm) = partition (\ l -> case l of
                        [x] -> isNat x || elem x
                               (displayTypes ++ globalCommands
                                ++ nodeCommands ++ edgeCommands)
                        _ -> False) q
           (q2, qr) = partition (\ l -> case l of
                        [x, y] -> elem x (["dg", "id", "session"]
                                          ++ nodeCommands ++ edgeCommands)
                                   && isNat y
                                  || x == "command" &&
                                     elem y globalCommands
                                  || x == "format" && elem y displayTypes
                        _ -> False) qm
           (fs, r1) = partition (`elem` displayTypes) $ map head q1
           (gs, r2) = partition (`elem` globalCommands) r1
           (ns, r3) = partition (`elem` nodeCommands) r2
           (es, is) = partition (`elem` edgeCommands) r3
           (fs2, p1) = partition ((== "format") . head) q2
           (cs2, p2) = partition ((== "command") . head) p1
           (is2, p3) = partition ((`elem` ["dg", "session"]) . head) p2
           (ns2, p4) = partition ((`elem` nodeCommands) . head) p3
           (es2, ids) = partition ((`elem` edgeCommands) . head) p4
           snds = map $ head . tail
           afs = nubOrd $ fs ++ snds fs2
           ags = nubOrd $ gs ++ snds cs2
           ans = nubOrd $ ns ++ map head ns2
           aes = nubOrd $ es ++ map head es2
           ais = nubOrd $ is ++ snds is2
           aids = nubOrd . snds $ ns2 ++ es2 ++ ids
           mi = fmap read $ listToMaybe ais
       in if null qr && length ais < 2 then case (afs, ags, ans, aes, aids) of
         (_, [], [], [], []) -> if length afs > 1
           then Left $ "non-unique format " ++ show afs
           else Right (mi, DisplayQuery $ listToMaybe afs)
         (_, c : r, [], [], _) -> if null r
           then Right (mi, GlobCmdQuery c)
           else Left $ "non-unique command " ++ show r
         (_, [], _, [], i : s) -> if null s && length ans < 2 then
           Right (mi, NodeQuery (read i) $ listToMaybe ans)
           else Left $ "non-unique node " ++ show (ans ++ aids)
         (_, [], [], e : r, i : s) -> if null r && null s then
           Right (mi, EdgeQuery (EdgeId $ read i) e)
           else Left $ "non-unique edge " ++ show (aes ++ aids)
         _ -> Left $ "non-unique query " ++ show q
       else Left $ if null qr then "non-unique dg " ++ show q else
                       "ill-formed query " ++ show qr
