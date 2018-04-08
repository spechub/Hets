{- |
Module      :  ./PGIP/Query.hs
Description :  hets server queries
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

query strings
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

import Common.Utils

import PGIP.ReasoningParameters
import PGIP.Shared
import Control.Exception

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as Map

import Common.Percent

import Driver.Options

ppList :: [String]
ppList = map (show . PrettyOut) prettyList ++ ["pdf"]

displayTypes :: [String]
displayTypes =
  ["svg", "xml", "json", "dot", "symbols", "session"] ++ ppList

comorphs :: [String]
comorphs = ["provers", "translations"]

data NodeCmd = Node | Info | Theory | Symbols | Translate String
  deriving (Show, Eq)

nodeCmds :: [NodeCmd]
nodeCmds = [Node, Info, Theory, Symbols]

showNodeCmd :: NodeCmd -> String
showNodeCmd = map toLower . show

nodeCommands :: [String]
nodeCommands = map showNodeCmd nodeCmds ++ comorphs ++ ["prove"]

proveParams :: [String]
proveParams = ["timeout", "include", "prover", "translation", "theorems",
  "axioms", "includeDetails", "includeProof"]

edgeCommands :: [String]
edgeCommands = ["edge"]

knownQueryKeys :: [String]
knownQueryKeys = displayTypes ++ nodeCommands ++ proveParams ++ edgeCommands
  ++ ["format", "autoproof", "consistency", "dg", "name", "id"]

-- Lib- and node name can be IRIs now (the query id is the session number)
data DGQuery = DGQuery
  { queryId :: Int
  , optQueryLibPath :: Maybe String
  }
  | NewDGQuery
  { queryLib :: FilePath
  , commands :: [String]
  } deriving Show

data Query = Query
  { dgQuery :: DGQuery
  , queryKind :: QueryKind
  } deriving Show

type NodeIdOrName = Either Int String

type QueryPair = (String, Maybe String)

showQuery :: [QueryPair] -> String
showQuery = ('?' :) . intercalate "&" . map (\ (s, ms) ->
  encode s ++ maybe "" (('=' :) . encode) ms)

showPath :: [String] -> String
showPath = intercalate "/" . map encode

showPathQuery :: [String] -> [QueryPair] -> String
showPathQuery p q = showPath p ++ if null q then "" else showQuery q

data QueryKind =
    DisplayQuery (Maybe String)
  | DGTranslation String
  | GlobCmdQuery String
  | GlProvers ProverMode (Maybe String)
  | GlTranslations
  | GlShowProverWindow ProverMode
  | GlAutoProveREST ProverMode ReasoningParameters
  | GlAutoProve ProveCmd
  | NodeQuery NodeIdOrName NodeCommand
  | EdgeQuery Int String deriving (Show, Eq)

data ProveCmd = ProveCmd
  { pcProverMode :: ProverMode
  , pcInclTheorems :: Bool
  , pcProver :: Maybe String
  , pcTranslation :: Maybe String
  , pcTimeout :: Maybe Int
  , pcTheoremsOrNodes :: [String]
  , pcXmlResult :: Bool
  , pcAxioms :: [String] } deriving (Show, Eq)

data NodeCommand =
    NcCmd NodeCmd
  | NcProvers ProverMode (Maybe String) -- optional comorphism
  | NcTranslations (Maybe String) -- optional prover name
  | ProveNode ProveCmd deriving (Show, Eq)

-- | the path is not empty and leading slashes are removed
anaUri :: [String] -> [QueryPair] -> [String] -> Either String Query
anaUri pathBits query globals = case anaQuery query globals of
    Left err -> Left err
    Right (mi, qk) -> let path = intercalate "/" pathBits in
     case (mi, readMaybe path) of
      (Just i, Just j) | i /= j -> Left "different dg ids"
      (_, mj) -> Right $ Query
        (case catMaybes [mi, mj] of
          [] -> NewDGQuery path []
          i : _ -> DGQuery i $ if isJust mj then Nothing else Just path)
        qk

isNat :: String -> Bool
isNat s = all isDigit s && not (null s) && length s < 11

getSwitches :: [QueryPair] -> Either String ([QueryPair], [(String, Flag)])
getSwitches qs = case qs of
  [] -> Right ([], [])
  q@(s, mv) : r ->
    let eith = getSwitches r
    in case lookup s optionFlags of
      Just f -> case mv of
        Just v | notElem (map toLower v) ["on", "t", "true", "1"] ->
          Left $ "query flag can only be switched on: " ++ s ++ "=" ++ v
        _ -> case eith of
          Right (qr, ps) -> Right (qr, (s, f) : ps)
          err -> err
      Nothing -> case eith of
        Right (qr, ps) -> Right (q : qr, ps)
        err -> err

-- due to the error calls in the option parsers this needs to be in the IO monad
getArgFlags :: [QueryPair]
  -> IO (Either String ([QueryPair], [(String, String)], [Flag]))
getArgFlags qs = case qs of
  [] -> return $ Right ([], [], [])
  q@(s, mv) : r -> do
    eith <- getArgFlags r
    case lookup s optionArgs of
     Just p -> case mv of
       Nothing -> return . Left $ "missing value for query argument: " ++ s
       Just v -> do
         eith2 <- try $ evaluate $ p v
         case eith2 :: Either ErrorCall Flag of
           Right f -> case eith of
               Right (qr, vs, fs) -> return $ Right (qr, (s, v) : vs, f : fs)
               err -> return err
           Left _ ->
             return . Left $ "illegal value for option: " ++ s ++ "=" ++ v
     Nothing -> case eith of
       Right (qr, vs, fs) -> return $ Right (q : qr, vs, fs)
       err -> return err

-- | a leading question mark is removed, possibly a session id is returned
anaQuery :: [QueryPair] -> [String] -> Either String (Maybe Int, QueryKind)
anaQuery q' globals =
       let (atP, q'') = partition ((== "autoproof") . fst) q'
           (atC, q) = partition ((== "consistency") . fst) q''
           (q1, qm) = partition (\ l -> case l of
                        (x, Nothing) -> isNat x || elem x
                               (displayTypes ++ globals
                                ++ ["include", "autoproof"]
                                ++ nodeCommands ++ edgeCommands)
                        _ -> False) q
           (q2, qr) = partition (\ l -> case l of
                        (x, Just y) ->
                            elem x (["dg", "id", "session"]
                                    ++ edgeCommands)
                            && isNat y
                               || x == "command" &&
                                  elem y globals
                               || x == "format" && elem y displayTypes
                               || elem x ("name" : tail proveParams
                                          ++ nodeCommands)
                                  -- note: allows illegal timeout values
                               || x == "timeout"
                                  -- without timeout, see above
                        _ -> False) qm
           (fs, r1) = partition (`elem` displayTypes) $ map fst q1
           (gs, r2) = partition (`elem` globals) r1
           (ns, r3) = partition (`elem` nodeCommands) r2
           (es, r4) = partition (`elem` edgeCommands) r3
           (incls, is) = partition (== "include") r4
           (fs2, p1) = partition ((== "format") . fst) q2
           (cs2, p2) = partition ((== "command") . fst) p1
           (is2, p3) = partition ((`elem` ["dg", "session"]) . fst) p2
           (ns2, p4) = partition ((`elem` nodeCommands) . fst) p3
           (es2, p5) = partition ((`elem` edgeCommands) . fst) p4
           (nns, p6) = partition ((== "name") . fst) p5
           (ids, pps) = partition ((== "id") . fst) p6
           snds = mapMaybe snd
           afs = nubOrd $ fs ++ snds fs2
           ags = nubOrd $ gs ++ snds cs2
           ans = nubOrd $ ns ++ map fst ns2
           aes = nubOrd $ es ++ map fst es2
           ais = nubOrd $ is ++ snds is2
           aids = nubOrd . snds $ ns2 ++ es2 ++ ids ++ nns
           mi = fmap read $ listToMaybe ais
           (theorems, qqr) = partition ((== Just "on") . snd) qr
           noPP = null pps && null incls && null theorems
       -- TODO i kind of abused this functions structure for autoproofs here
       in if not $ null atP then Right (mi, GlShowProverWindow GlProofs) else
          if not $ null atC then Right (mi, GlShowProverWindow GlConsistency)
          else
          if null qqr && length ais < 2 then case (afs, ags, ans, aes, aids) of
         (_, [], [], [], []) | noPP -> if length afs > 1
           then Left $ "non-unique format " ++ show afs
           else Right (mi, DisplayQuery $ listToMaybe afs)
         (_, c : r, [], [], []) | noPP -> if null r
           then Right (mi, GlobCmdQuery c)
           else Left $ "non-unique command " ++ show r
         (_, [], _, [], [_]) -> fmap (\ qk -> (mi, qk)) $
           anaNodeQuery ans (getIdOrName ids nns ns2) (map fst theorems)
             incls pps
         (_, [], [], e : r, i : s) | noPP ->
           if null r && null s && null nns && null ns2
           then Right (mi, EdgeQuery (read i) e)
           else Left $ "non-unique edge " ++ show (aes ++ aids)
         _ -> Left $ "non-unique query " ++ show q
       else Left $ if null qqr then "non-unique dg " ++ show q else
                       "ill-formed query " ++ show qqr

getIdOrName :: [QueryPair] -> [QueryPair] -> [QueryPair] -> NodeIdOrName
getIdOrName ids nns ns2 = case ids of
  (_, Just v) : _ -> Left $ read v
  _ -> case nns of
    (_, Just v) : _ -> Right v
    _ -> case ns2 of
      (_, Just v) : _ -> if isNat v then Left $ read v else Right v
      _ -> error "getIdOrName"

escMap :: [(Char, Char)]
escMap = map (\ l -> let [f, s] = l in (f, s))
  [ "+P"
  , "&A"
  , "=E"
  , ";S"
  , " B"
  , "XX" ]

escStr :: String -> String
escStr = concatMap (\ c -> case Map.lookup c $ Map.fromList escMap of
    Nothing -> [c]
    Just e -> ['X', e])

unEsc :: String -> String
unEsc s = let m = Map.fromList $ map (\ (a, b) -> (b, a)) escMap
  in case s of
  "" -> ""
  'X' : c : r -> Map.findWithDefault c c m : unEsc r
  c : r -> c : unEsc r

decodePlus :: Char -> Char
decodePlus c = if c == '+' then ' ' else c

decodeQuery :: String -> String
decodeQuery = map decodePlus . decode

getFragOfCode :: String -> String
getFragOfCode = getFragment . decodeQuery

getFragment :: String -> String
getFragment s = case dropWhile (/= '#') s of
  _ : t -> t
  "" -> s

anaNodeQuery :: [String] -> NodeIdOrName -> [String] -> [String]
  -> [QueryPair] -> Either String QueryKind
anaNodeQuery ans i moreTheorems incls pss =
  let pps = foldr (\ l -> case l of
                (x, Just y) -> ((x, y) :)
                _ -> id) [] pss
      incl = lookup "include" pps
      trans = fmap decodeQuery $ lookup "translation" pps
      prover = lookup "prover" pps
      theorems = map unEsc moreTheorems
          ++ case lookup "theorems" pps of
        Nothing -> []
        Just str -> map unEsc $ splitOn ' ' $ decodeQuery str
      timeLimit_ = maybe Nothing readMaybe $ lookup "timeout" pps
      pp = ProveNode $ ProveCmd GlProofs (not (null incls) || case incl of
        Nothing -> True
        Just str -> map toLower str `notElem` ["f", "false"])
        prover trans timeLimit_ theorems False []
      noPP = null incls && null pps
      noIncl = null incls && isNothing incl && isNothing timeLimit_
      cmds = map (\ a -> (showNodeCmd a, a)) nodeCmds
  in case ans of
       [] -> Right $ NodeQuery i
         $ if noPP then NcCmd Node else pp
       [cmd] -> case cmd of
         "prove" -> Right $ NodeQuery i pp
         "provers" | noIncl && isNothing prover ->
            Right $ NodeQuery i $ NcProvers GlProofs trans
         "translations" | noIncl && isNothing trans ->
            Right $ NodeQuery i $ NcTranslations prover
         _ -> case lookup cmd cmds of
           Just nc | noPP -> Right $ NodeQuery i $ NcCmd nc
           _ -> Left $ "unknown node command '" ++ cmd ++ "' "
                ++ shows incls " " ++ show pss
       _ -> Left $ "non-unique node command " ++ show ans
