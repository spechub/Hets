{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  run hets as server
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}

module PGIP.Server (hetsServer) where

import PGIP.Output.Formatting
import PGIP.Output.Mime
import PGIP.Output.Proof
import PGIP.Output.Translations
import qualified PGIP.Output.Provers as OProvers

import PGIP.Query as Query

import Driver.Options
import Driver.ReadFn
import Driver.Version

import Network.Wai.Handler.Warp
import Network.HTTP.Types
import Control.Monad.Trans (lift, liftIO)
#ifdef WARP1
import Control.Monad.Trans.Resource
import Data.Conduit.Lazy (lazyConsume)
#endif
import qualified Data.Text as T

import Network.Wai
import Network.Wai.Parse

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as B8

import Static.AnalysisLibrary
import Static.ApplyChanges
import Static.ComputeTheory
import Static.DevGraph
import Static.DgUtils
import Static.DotGraph
import Static.FromXml
import Static.GTheory
import Static.History (changeDGH)
import Static.PrintDevGraph
import qualified Static.ToJson as ToJson
import Static.ToXml as ToXml

import Logic.LGToXml

import Syntax.ToXml
import Syntax.Print_AS_Structured

import Interfaces.Command
import Interfaces.CmdAction
import Interfaces.GenericATPState

import Comorphisms.LogicGraph

import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Logic

import Proofs.AbstractState as AbsState
import Proofs.ConsistencyCheck

import Text.ParserCombinators.Parsec (parse)

import Text.XML.Light
import Text.XML.Light.Cursor

import Common.AutoProofUtils
import Common.Doc
import Common.DocUtils (pretty, showGlobalDoc, showDoc)
import Common.ExtSign (ExtSign (..))
import Common.GtkGoal
import Common.Json (Json (..), pJson, ppJson)
import Common.LibName
import Common.PrintLaTeX
import Common.Result
import Common.ResultT
import Common.ToXml
import Common.Utils
import Common.XUpdate

import Control.Monad

import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.CaseInsensitive as CI
import Data.Char
import Data.IORef
import Data.Function
import Data.List
import Data.Maybe
import Data.Ord
import Data.Graph.Inductive.Graph (lab)
import Data.Time.Clock
import Data.Time.LocalTime

import System.Random
import System.Directory
import System.Exit
import System.FilePath
import System.IO

data Session = Session
  { sessLibEnv :: LibEnv
  , sessLibName :: LibName
  , sessPath :: [String]
  , sessKey :: Int
  , sessStart :: UTCTime
  , lastAccess :: UTCTime
  , usage :: Int }

data UsedAPI = OldWebAPI | RESTfulAPI deriving (Show, Eq, Ord)

type SessMap = Map.Map [String] Session
type Cache = IORef (IntMap.IntMap Session, SessMap)

randomKey :: IO Int
randomKey = randomRIO (100000000, 999999999)

sessGraph :: DGQuery -> Session -> Maybe (LibName, DGraph)
sessGraph dgQ s =
  let le = sessLibEnv s
      ln = sessLibName s
  in case dgQ of
  DGQuery _ (Just path) ->
      find (\ (n, _) -> libToFileName n == path)
        $ Map.toList le
  _ -> fmap (\ dg -> (ln, dg)) $ Map.lookup ln le

getVal :: [QueryPair] -> String -> Maybe String
getVal qs = fromMaybe Nothing . (`lookup` qs)

getIP4 :: String -> [String]
getIP4 = splitOn '.' . takeWhile (\ c -> isDigit c || c == '.')

matchIP4 :: [String] -> [String] -> Bool
matchIP4 ip mask = case mask of
  [] -> True
  ft : rt -> case ip of
    [] -> False -- mask too long or IP too short
    d : s -> (null ft || ft == d) && matchIP4 rt s

matchWhite :: [String] -> [[String]] -> Bool
matchWhite ip l = null l || any (matchIP4 ip) l

#ifdef WARP1
type RsrcIO a = ResourceT IO a
#else
type RsrcIO a = IO a
#endif

#ifdef WARP3
type WebResponse = (Response -> IO ResponseReceived) -> IO ResponseReceived
#else
type WebResponse = (Response -> RsrcIO Response) -> RsrcIO Response
#endif

hetsServer :: HetcatsOpts -> IO ()
hetsServer opts1 = do
  tempDir <- getTemporaryDirectory
  let tempLib = tempDir </> "MyHetsLib"
      permFile = tempDir </> "empty.txt"
      opts = opts1 { libdirs = tempLib : libdirs opts1 }
      port1 = listen opts1
      port = if port1 < 0 then 8000 else port1
      wl = whitelist opts1
      bl = blacklist opts1
      prList ll = intercalate ", " $ map (intercalate ".") ll
  createDirectoryIfMissing False tempLib
  writeFile permFile ""
  unless (null wl) . appendFile permFile
    $ "white list: " ++ prList wl ++ "\n"
  unless (null bl) . appendFile permFile
    $ "black list: " ++ prList bl ++ "\n"
  sessRef <- newIORef (IntMap.empty, Map.empty)
  putIfVerbose opts 1 $ "hets server is listening on port " ++ show port
  putIfVerbose opts 2 $ "for more information look into file: " ++ permFile
#ifdef WARP3
  runSettings (setPort port $ setTimeout 86400 defaultSettings) $ \ re respond -> do
#else
  run port $ \ re -> do
   let respond = liftIO . return
#endif
   let rhost = shows (remoteHost re) "\n"
       ip = getIP4 rhost
       white = matchWhite ip wl
       black = any (matchIP4 ip) bl
       splitQuery = map (\ (bs, ms) -> (B8.unpack bs, fmap B8.unpack ms))
         $ queryString re
       pathBits = map T.unpack $ pathInfo re
       meth = B8.unpack (requestMethod re)
       query = showPathQuery pathBits splitQuery
   liftIO $ do
     time <- getCurrentTime
     createDirectoryIfMissing False tempLib
     (m, _) <- readIORef sessRef
     appendFile permFile rhost
     unless black $ if white then do
         appendFile permFile $ shows time " sessions: "
                    ++ shows (IntMap.size m) "\n"
         appendFile permFile $ shows (requestHeaders re) "\n"
         unless (null query) $ appendFile permFile $ query ++ "\n"
       else appendFile permFile "not white listed\n"
   if not white || black then respond $ mkResponse "" status403 ""
    -- if path could be a RESTful request, try to parse it
    else do
     eith <- liftIO $ getArgFlags splitQuery
     case eith of
       Left err -> queryFail err respond
       Right (qr, vs, fs) ->
         let eith2 = getSwitches qr
         in case eith2 of
         Left err -> queryFail err respond
         Right (qr2, fs2) ->
           let newOpts = foldl makeOpts opts $ fs ++ map snd fs2
           in if isRESTful pathBits then do
              requestBodyParams <- parseRequestParams re
              let unknown = filter (`notElem` allQueryKeys) $ map fst qr2
              if null unknown
                then parseRESTful newOpts sessRef pathBits
                    (map fst fs2 ++ map (\ (a, b) -> a ++ "=" ++ b) vs)
                    qr2 requestBodyParams meth respond
                else queryFail ("unknown query key(s): " ++ show unknown)
                               respond
           -- only otherwise stick to the old response methods
           else oldWebApi newOpts tempLib permFile sessRef re pathBits qr2
             meth respond
parseRequestParams :: Request -> RsrcIO Json
parseRequestParams request =
  let
    noParams :: Json
    noParams = JNull

    parseJson :: String -> Maybe Json
    parseJson s = case parse pJson "" s of
      Left _ -> Nothing
      Right json -> Just json

    lookupHeader :: String -> Maybe String
    lookupHeader s =
      liftM B8.unpack $ lookup (CI.mk $ B8.pack s) $ requestHeaders request

    formParams :: RsrcIO (Maybe Json)
    formParams =
      let toJsonObject :: [(B8.ByteString, B8.ByteString)] -> String
          toJsonObject assocList = "{"
            ++ intercalate ", " (map (\ (k, v) ->
                  show k ++ ": " ++ jsonStringOrArray v) assocList)
            ++ "}"
          jsonStringOrArray str =
            if B8.head str == '[' then B8.unpack str else show str
      in do
        (formDataB8, _) <- parseRequestBody lbsBackEnd request
        return $ parseJson $ toJsonObject formDataB8

    jsonBody :: RsrcIO (Maybe Json)
    jsonBody = liftM (parseJson . B8.unpack) $ receivedRequestBody

    receivedRequestBody :: RsrcIO B8.ByteString
#ifdef WARP3
    receivedRequestBody = requestBody request
#else
    receivedRequestBody = liftM (B8.pack . BS.unpack) $ lazyRequestBody request
#endif

#ifdef WARP1
    lazyRequestBody :: Request -> ResourceT IO BS.ByteString
    lazyRequestBody = fmap BS.fromChunks . lazyConsume . requestBody
#endif
  in
    liftM (fromMaybe noParams) $ case lookupHeader "Content-Type" of
      Just "application/json" -> jsonBody
      Just "multipart/form-data" -> formParams
      _ -> formParams

-- | the old API that supports downloading files and interactive stuff
oldWebApi :: HetcatsOpts -> FilePath -> FilePath -> Cache -> Request -> [String]
  -> [QueryPair] -> String -> WebResponse
oldWebApi opts tempLib permFile sessRef re pathBits splitQuery meth respond
  = case meth of
      "GET" -> if isJust $ lookup "menus" splitQuery
         then mkMenuResponse respond else do
         let path = intercalate "/" pathBits
         dirs@(_ : cs) <- liftIO $ getHetsLibContent opts path splitQuery
         if not (null cs) || null path then mkHtmlPage path dirs respond
           -- AUTOMATIC PROOFS (parsing)
           else if isJust $ getVal splitQuery "autoproof" then
             let qr k = Query (DGQuery k Nothing) $
                   anaAutoProofQuery splitQuery in do
               Result ds ms <- liftIO $ runResultT
                 $ case readMaybe $ head pathBits of
                 Nothing -> fail "cannot read session id for automatic proofs"
                 Just k' -> getHetsResult opts [] sessRef (qr k')
                              Nothing OldWebAPI proofFormatterOptions
               respond $ case ms of
                 Nothing -> mkResponse textC status422 $ showRelDiags 1 ds
                 Just (t, s) -> mkOkResponse t s
           -- AUTOMATIC PROOFS E.N.D.
           else getHetsResponse opts [] sessRef pathBits splitQuery respond
      "POST" -> do
        (params, files) <- parseRequestBody lbsBackEnd re
        mTmpFile <- case lookup "content"
                   $ map (\ (a, b) -> (B8.unpack a, b)) params of
              Nothing -> return Nothing
              Just areatext -> let content = B8.unpack areatext in
                if all isSpace content then return Nothing else liftIO $ do
                   tmpFile <- getTempFile content "temp.het"
                   copyPermissions permFile tmpFile
                   return $ Just tmpFile
        let res tmpFile =
              getHetsResponse opts [] sessRef [tmpFile] splitQuery respond
            mRes = maybe (queryFail "nothing submitted" respond)
              res mTmpFile
        case files of
          [] -> if isJust $ getVal splitQuery "prove" then
               getHetsResponse opts [] sessRef pathBits
                 (splitQuery ++ map (\ (a, b)
                 -> (B8.unpack a, Just $ B8.unpack b)) params) respond
            else mRes
          [(_, f)] | isNothing $ lookup updateS splitQuery -> do
           let fn = takeFileName $ B8.unpack $ fileName f
           if any isAlphaNum fn then do
             let tmpFile = tempLib </> fn
             liftIO $ BS.writeFile tmpFile $ fileContent f
             liftIO $ copyPermissions permFile tmpFile
             maybe (res tmpFile) res mTmpFile
            else mRes
          _ -> getHetsResponse
                 opts (map snd files) sessRef pathBits splitQuery respond
      _ -> respond $ mkResponse "" status400 ""

-- extract what we need to know from an autoproof request
anaAutoProofQuery :: [QueryPair] -> QueryKind
anaAutoProofQuery splitQuery = let
  lookup2 = getVal splitQuery
  prover = lookup2 "prover"
  trans = lookup2 "translation"
  timeout = lookup2 "timeout" >>= readMaybe
  include = maybe False (== "on") $ lookup2 "includetheorems"
  nodeSel = filter (/= "includetheorems")
      $ map fst $ filter ((== Just "on") . snd) splitQuery
  axioms = mSplitOnComma $ lookup2 "axioms"
  prOrCons = case lookup2 "autoproof" of
    Just "proof" -> GlProofs
    Just "cons" -> GlConsistency
    err -> error $ "illegal autoproof method: " ++ show err
  in GlAutoProve $
        ProveCmd prOrCons include prover trans timeout nodeSel False axioms

-- quick approach to whether or not the query can be a RESTful request
isRESTful :: [String] -> Bool
isRESTful pathBits = case pathBits of
  [] -> False
  [h] | elem h ["version", "robots.txt"] -> True
  h : _ -> elem h listRESTfulIdentifiers

listRESTfulIdentifiers :: [String]
listRESTfulIdentifiers =
  [ "libraries", "sessions", "menus", "filetype", "hets-lib", "dir"]
  ++ nodeEdgeIdes ++ newRESTIdes
  ++ ["available-provers"]

nodeEdgeIdes :: [String]
nodeEdgeIdes = ["nodes", "edges"]

newRESTIdes :: [String]
newRESTIdes =
  [ "dg", "translations", "provers", "consistency-checkers", "prove"
  , "consistency-check" ]

queryFail :: String -> WebResponse
queryFail msg respond = respond $ mkResponse textC status400 msg

allQueryKeys :: [String]
allQueryKeys = [updateS, "library", "consistency-checker"]
  ++ globalCommands ++ knownQueryKeys


data RequestBodyParam = Single String | List [String]

-- query is analysed and processed in accordance with RESTful interface
parseRESTful :: HetcatsOpts -> Cache -> [String] -> [String] -> [QueryPair]
  -> Json -> String -> WebResponse
parseRESTful
  opts sessRef pathBits qOpts splitQuery requestBodyParams meth respond = let
  {- some parameters from the paths query part might be needed more than once
  (when using lookup upon querybits, you need to unpack Maybe twice) -}
  lookupQueryStringParam :: String -> Maybe String
  lookupQueryStringParam = getVal splitQuery

  lookupBodyParam :: String -> Json -> Maybe RequestBodyParam
  lookupBodyParam key json = case json of
    JObject pairs -> case lookup key pairs of
      Just (JArray a) -> Just $ List $ map (read . ppJson) a
      Just v -> Just $ Single $ read $ ppJson v
      _ -> Nothing
    _ -> Nothing

  lookupSingleParam :: String -> Maybe String
  lookupSingleParam key = case meth of
    "GET" -> lookupQueryStringParam key
    _ -> case lookupBodyParam key requestBodyParams of
          Just (Single s) -> Just s
          _ -> Nothing

  lookupListParam :: String -> [String]
  lookupListParam key = case meth of
    "GET" -> mSplitOnComma $ lookupQueryStringParam key
    _ -> case lookupBodyParam key requestBodyParams of
          Just (List ps) -> ps
          _ -> []

  isParamTrue :: Bool -> String -> Bool
  isParamTrue def key = case fmap (map toLower) $ lookupSingleParam key of
    Nothing -> def
    Just "true" -> True
    _ -> False

  session = lookupSingleParam "session" >>= readMaybe
  library = lookupSingleParam "library"
  format = lookupSingleParam "format"
  nodeM = lookupSingleParam "node"
  includeDetails = isParamTrue True "includeDetails"
  includeProof = isParamTrue True "includeProof"
  theorems = lookupListParam "theorems"
  transM = lookupSingleParam "translation"
  proverM = lookupSingleParam "prover"
  consM = lookupSingleParam "consistency-checker"
  inclM = lookupSingleParam "include"
  axioms = lookupListParam "axioms"
  incl = maybe False (\ s ->
              notElem (map toLower s) ["f", "false"]) inclM
  timeout = lookupSingleParam "timeout" >>= readMaybe
  queryFailure = queryFail
    ("this query does not comply with RESTful interface: "
    ++ showPathQuery pathBits splitQuery) respond
  -- since used more often, generate full query out of nodeIRI and nodeCmd
  nodeQuery s = NodeQuery $ maybe (Right s) Left (readMaybe s :: Maybe Int)
  pfOptions = proofFormatterOptions
                { pfoIncludeProof = includeProof
                , pfoIncludeDetails = includeDetails
                }
  parseNodeQuery :: Monad m => String -> Int -> m NodeCommand -> m Query.Query
  parseNodeQuery p sId ncmd = ncmd >>= let
      in return . Query (DGQuery sId (Just p)) . nodeQuery (getFragment p)
  -- call getHetsResult with the properly generated query (Final Result)
  getResponseAux myOpts qr = do
    Result ds ms <- liftIO $ runResultT $
      getHetsResult myOpts [] sessRef qr format RESTfulAPI pfOptions
    respond $ case ms of
      Nothing -> mkResponse textC status422 $ showRelDiags 1 ds
      Just (t, s) -> mkOkResponse t s
  getResponse = getResponseAux opts
  -- respond depending on request Method
  in case meth of
    rm | elem rm ["GET", "POST"] -> case pathBits of
      ["robots.txt"] -> respond $ mkOkResponse textC
        $ unlines ["User-agent: *", "Disallow: /"]
      -- show all menu options
      ["menus"] -> mkMenuResponse respond
      -- list files from directory
      "dir" : r -> do
        let path' = intercalate "/" r
        dirs <- liftIO $ getHetsLibContent opts path' splitQuery
        mkHtmlPage path' dirs respond
      ["version"] -> respond $ mkOkResponse textC hetcats_version
      ["available-provers"] ->
         liftIO (usableProvers logicGraph)
         >>= respond . mkOkResponse xmlC . ppTopElement
      -- get dgraph from file
      "filetype" : libIri : _ -> mkFiletypeResponse opts libIri respond
      "hets-lib" : r -> let file = intercalate "/" r in
        getResponse $ Query (NewDGQuery file []) $ DisplayQuery format
      -- get library (complies with get/hets-lib for now)
      ["libraries", libIri, "development_graph"] ->
        getResponse $ Query (NewDGQuery libIri []) $ DisplayQuery format
      -- get previously created session
      "sessions" : sessId : cmd -> case readMaybe sessId of
          Nothing -> queryFail ("failed to read session number from " ++ sessId)
            respond
          Just sId ->
            (case nodeM of
              Just ndIri -> parseNodeQuery ndIri sId $ case cmd of
                ["provers"] -> return $ NcProvers GlProofs transM
                ["translations"] -> return $ NcTranslations Nothing
                _ -> fail $ "unknown node command for a GET-request: "
                      ++ intercalate "/" cmd
              Nothing -> fmap (Query (DGQuery sId Nothing)) $ case cmd of
                [] -> return $ DisplayQuery format
                ["provers"] -> return $ GlProvers GlProofs transM
                ["translations"] -> return GlTranslations
                _ -> fail $ "unknown global command for a GET-request: "
                  ++ intercalate "/" cmd) >>= getResponse
      -- get node or edge view
      nodeOrEdge : p : c | elem nodeOrEdge nodeEdgeIdes -> let
        iriPath = takeWhile (/= '#') p
        dgQ = maybe (NewDGQuery (fromMaybe iriPath library) [])
                 (`DGQuery` library) session
        f = getFragment p
        in case elemIndex nodeOrEdge nodeEdgeIdes of
          Just 0 -> let
            i = maybe (Right f) Left $ readMaybe f in
            getResponse $ Query dgQ $ NodeQuery i $ case c of
                ["theory"] -> NcCmd Query.Theory
                _ -> NcCmd Query.Info
          Just 1 -> case readMaybe f of
            Just i -> getResponse $ Query dgQ $ EdgeQuery i "edge"
            Nothing -> queryFail ("failed to read edgeId from " ++ f) respond
          _ -> error $ "PGIP.Server.elemIndex " ++ nodeOrEdge
      newIde : libIri : rest ->
        let cmdOptList = filter (/= "") rest
            (optFlags, cmdList) = partition (`elem` map fst optionFlags)
              cmdOptList
            newOpts = foldl makeOpts opts $ mapMaybe (`lookup` optionFlags)
              optFlags
        in if elem newIde newRESTIdes && all (`elem` globalCommands) cmdList
        then getResponseAux newOpts . Query (NewDGQuery libIri $ cmdList
            ++ Set.toList (Set.fromList $ optFlags ++ qOpts))
         $ case newIde of
           "translations" -> case nodeM of
             Nothing -> GlTranslations
             Just n -> nodeQuery n $ NcTranslations Nothing
           _ | elem newIde ["provers", "consistency-checkers"] ->
             let pm = if newIde == "provers" then GlProofs else GlConsistency
             in case nodeM of
             Nothing -> GlProvers pm transM
             Just n -> nodeQuery n $ NcProvers pm transM
           _ | elem newIde ["prove", "consistency-check"] ->
             let isProve = newIde == "prove"
                 pm = if isProve then GlProofs else GlConsistency
                 pc = ProveCmd pm
                        (not (isProve && isJust inclM) || incl)
                        (if isProve then proverM else consM)
                        transM timeout theorems True axioms
             in case nodeM of
             Nothing -> GlAutoProve pc
             Just n -> nodeQuery n $ ProveNode pc
           _ -> DisplayQuery (Just $ fromMaybe "xml" format)
        else queryFailure
      _ -> queryFailure
    "PUT" -> case pathBits of
      {- execute global commands
         TODO load other library ??? -}
      ["libraries", libIri, "proofs", prId, cmd] ->
         case readMaybe prId of
           Nothing -> queryFail ("failed to read sessionId from " ++ prId)
             respond
           Just sessId -> let
             dgQ = DGQuery sessId $ Just libIri in
             getResponse $ Query dgQ $ GlobCmdQuery cmd
      -- execute a proof or calculus request
      ["sessions", sessId, cmd] -> case readMaybe sessId of
        Nothing -> queryFail ("failed to read sessionId from " ++ sessId)
          respond
        Just sId -> case cmd of
          "prove" ->
            let pc = ProveCmd GlProofs incl proverM transM timeout [] False
                        axioms
            in case nodeM of
                -- prove all nodes if no singleton is selected
                Nothing -> return $ Query (DGQuery sId Nothing)
                  $ GlAutoProve pc
                -- otherwise run prover for single node only
                Just ndIri -> parseNodeQuery ndIri sId $ return
                  $ ProveNode pc
              >>= getResponse
          -- on other cmd look for (optional) specification of node or edge
          _ -> case (nodeM, lookupSingleParam "edge") of
              -- fail if both are specified
              (Just _, Just _) ->
                fail "please specify only either node or edge"
              -- call command upon a single node
              (Just ndIri, Nothing) -> parseNodeQuery ndIri sId
                $ case lookup cmd $ map (\ a -> (showNodeCmd a, a)) nodeCmds of
                  Just nc -> return $ NcCmd nc
                  _ -> fail $ "unknown node command '" ++ cmd ++ "' "
              -- call (the only) command upon a single edge
              (Nothing, Just edIri) -> case readMaybe $ getFragOfCode edIri of
                Just i -> return $ Query (DGQuery sId Nothing)
                  $ EdgeQuery i "edge"
                Nothing ->
                  fail $ "failed to read edgeId from edgeIRI: " ++ edIri
              -- call of global command
              _ -> return $ Query (DGQuery sId Nothing) $ GlobCmdQuery cmd
           >>= getResponse
      -- fail if request doesn't comply
      _ -> queryFailure
    {- create failure response if request method is not known
    (should never happen) -}
    _ -> respond $ mkResponse "" status400 ""

mSplitOnComma :: Maybe String -> [String]
mSplitOnComma mstr = case mstr of
  Nothing -> []
  Just str -> splitOn ',' str

mkMenuResponse :: WebResponse
mkMenuResponse respond =
  respond $ mkOkResponse xmlC $ ppTopElement $ unode "menus" mkMenus

mkMenus :: [Element]
mkMenus = menuTriple "" "Get menu triples" "menus"
  : menuTriple "/DGraph" updateS updateS
  : map (\ (c, _) -> menuTriple "/" (menuTextGlobCmd c) $ cmdlGlobCmd c)
    allGlobLibAct
  ++ map (\ nc -> menuTriple "/DGraph/DGNode" ("Show " ++ nc) nc) nodeCommands
  ++ [menuTriple "/DGraph/DGLink" "Show edge info" "edge"]

status422 :: Status
status422 = Status 422 $ B8.pack "Unprocessable Entity"

mkFiletypeResponse :: HetcatsOpts -> String -> WebResponse
mkFiletypeResponse opts libIri respond = do
  res <- liftIO $ getContentAndFileType opts libIri
  respond $ case res of
    Left err -> mkResponse textC status422 err
    Right (mr, _, fn, _) -> case mr of
      Nothing -> mkResponse textC status422 $ fn ++ ": unknown file type"
      Just r -> mkOkResponse textC $ fn ++ ": " ++ r

menuTriple :: String -> String -> String -> Element
menuTriple q d c = unode "triple"
                [ unode "xquery" q
                , unode "displayname" d
                , unode "command" c ]

metaRobots :: Element
metaRobots = add_attrs
  [mkNameAttr "robots", mkAttr "content" "noindex,nofollow"]
  $ unode "meta" ()

mkHtmlString :: FilePath -> [Element] -> String
mkHtmlString path dirs = htmlHead ++ mkHtmlElem
  ("Listing of" ++ if null path then " repository" else ": " ++ path)
  (unode "h1" ("Hets " ++ hetcats_version) : unode "p"
     [ bold "Hompage:"
     , aRef "http://hets.eu" "hets.eu"
     , bold "Contact:"
     , aRef "mailto:hets-devel@informatik.uni-bremen.de"
       "hets-devel@informatik.uni-bremen.de" ]
   : headElems path ++ [unode "ul" dirs])

mkHtmlElem :: String -> [Element] -> String
mkHtmlElem title = mkHtmlElemAux title [metaRobots]

mkHtmlElemAux :: String -> [Element] -> [Element] -> String
mkHtmlElemAux title headers body = ppElement $ unode "html"
      [ unode "head" $ unode "title" title : headers, unode "body" body ]

-- include a script within page
mkHtmlElemScript :: String -> String -> [Element] -> String
mkHtmlElemScript title scr =
  mkHtmlElemAux title [ metaRobots
  , add_attr (mkAttr "type" "text/javascript") . unode "script"
    . Text $ CData CDataRaw scr Nothing] -- scr must not be encoded!

mkHtmlPage :: FilePath -> [Element] -> WebResponse
mkHtmlPage path es respond = respond . mkOkResponse htmlC
  $ mkHtmlString path es

mkResponse :: String -> Status -> String -> Response
mkResponse ty st = responseLBS st
  (if null ty then [] else
#ifdef HTTPTYPES
      [headerContentType $ B8.pack ty]
#else
      [(hContentType, B8.pack ty)]
#endif
  ) . BS.pack

mkOkResponse :: String -> String -> Response
mkOkResponse ty = mkResponse ty status200

addSess :: Cache -> Session -> IO Int
addSess sessRef s = do
  let k = sessKey s
  atomicModifyIORef sessRef $ \ (m, lm) ->
       ((IntMap.insert k s m, Map.insert (sessPath s) s lm), k)

cleanUpCache :: Cache -> IO ()
cleanUpCache sessRef = do
  let mSize = 20
  time <- getCurrentTime
  atomicModifyIORef sessRef $ \ (m, lm) ->
    if Map.size lm < mSize then ((m, lm), ()) else
    let ss = drop (div mSize 2) . sortBy (cmpSess time) $ Map.elems lm
    in ((IntMap.fromList $ map (\ s -> (sessKey s, s)) ss
       , Map.fromList $ map (\ s -> (sessPath s, s)) ss), ())

cmpSess :: UTCTime -> Session -> Session -> Ordering
cmpSess curTime =
  let f s = let
        l = lastAccess s
        b = sessStart s
        d2 = utctDay curTime
        s2 = utctDayTime curTime
        d1 = utctDay l
        s1 = utctDayTime l
        u = usage s
        in if u <= 1 && d1 == d2 && s2 > secondsToDiffTime 3600 + s1
           then (u + 100, diffUTCTime l curTime)
           else (u, diffUTCTime b l)
  in on compare f

addNewSess :: Cache -> Session -> IO Int
addNewSess sessRef sess = do
  cleanUpCache sessRef
  k <- randomKey
  let s = sess { sessKey = k }
  addSess sessRef s

nextSess :: Session -> Cache -> LibEnv -> Int -> IO Session
nextSess sess sessRef newLib k = if k <= 0 then return sess else
    atomicModifyIORef sessRef
      (\ (m, lm) -> case IntMap.lookup k m of
      Nothing -> error "nextSess"
      Just s -> let newSess = s { sessLibEnv = newLib }
        in ((IntMap.insert k newSess m, lm), newSess))

ppDGraph :: DGraph -> Maybe PrettyType -> ResultT IO (String, String)
ppDGraph dg mt = let ga = globalAnnos dg in case optLibDefn dg of
    Nothing -> fail "parsed LIB-DEFN not avaible"
    Just ld ->
      let d = prettyLG logicGraph ld
          latex = renderLatex Nothing $ toLatex ga d
      in case mt of
      Just pty -> case pty of
        PrettyXml -> return
          (xmlC, ppTopElement $ xmlLibDefn logicGraph ga ld)
        PrettyAscii _ -> return (textC, renderText ga d ++ "\n")
        PrettyHtml -> return (htmlC, htmlHead ++ renderHtml ga d)
        PrettyLatex _ -> return ("application/latex", latex)
      Nothing -> lift $ do
         tmpDir <- getTemporaryDirectory
         tmpFile <- writeTempFile (latexHeader ++ latex ++ latexFooter)
           tmpDir "temp.tex"
         copyPermissions (tmpDir </> "empty.txt") tmpFile
         mapM_ (\ s -> do
            let sty = (</> "hetcasl.sty")
                f = sty s
            ex <- doesFileExist f
            when ex $ copyFile f $ sty tmpDir)
              [ "utils", "Hets/utils"
              , "/home/www.informatik.uni-bremen.de/cofi/hets-tmp" ]
         withinDirectory tmpDir $ do
           (ex1, out1, err1) <- executeProcess "pdflatex" [tmpFile] ""
           (ex2, out2, err2) <- executeProcess "pdflatex" [tmpFile] ""
           let pdfFile = replaceExtension tmpFile "pdf"
           pdf <- doesFileExist pdfFile
           if ex1 == ExitSuccess && ex2 == ExitSuccess && pdf then do
             pdfHdl <- openBinaryFile pdfFile ReadMode
             str <- hGetContents pdfHdl
             when (length str < 0) $ putStrLn "pdf file too large"
             hClose pdfHdl
             return (pdfC, str)
             else return (textC, "could not create pdf:\n"
                  ++ unlines [out1, err1, out2, err2])

increaseUsage :: Cache -> Session -> ResultT IO (Session, Int)
increaseUsage sessRef sess = do
  time <- lift getCurrentTime
  let s2 = sess { usage = usage sess + 1, lastAccess = time }
  k <- lift $ addSess sessRef s2
  return (s2, k)

getDGraph :: HetcatsOpts -> Cache -> DGQuery
  -> ResultT IO (Session, Int)
getDGraph opts sessRef dgQ = do
  (m, lm) <- lift $ readIORef sessRef
  case dgQ of
    NewDGQuery file cmdList -> do
      let cl = mapMaybe (\ s -> find ((== s) . cmdlGlobCmd)
                  $ map fst allGlobLibAct) cmdList
      mf <- lift $ getContentAndFileType opts file
      case mf of
        Left err -> fail err
        Right (_, mh, f, cont) -> case mh of
          Nothing -> fail $ "could determine checksum for: " ++ file
          Just h -> let q = file : h : cmdList in
            case Map.lookup q lm of
            Just sess -> increaseUsage sessRef sess
            Nothing -> do
              (ln, le1) <- if isDgXmlFile opts f cont
                then readDGXmlR opts f Map.empty
                else anaSourceFile logicGraph opts
                  { outputToStdout = False }
                  Set.empty emptyLibEnv emptyDG file
              le2 <- foldM (\ e c -> liftR
                  $ fromJust (lookup c allGlobLibAct) ln e) le1 cl
              time <- lift getCurrentTime
              let sess = Session
                    { sessLibEnv = le2
                    , sessLibName = ln
                    , sessPath = q
                    , sessKey = 0  -- to be updated by addNewSess
                    , sessStart = time
                    , lastAccess = time
                    , usage = 1 }
              k <- lift $ addNewSess sessRef sess
              return (sess, k)
    DGQuery k _ -> case IntMap.lookup k m of
      Nothing -> fail "unknown development graph"
      Just sess -> increaseUsage sessRef sess

getSVG :: String -> String -> DGraph -> ResultT IO String
getSVG title url dg = do
        (exCode, out, err) <- lift $ executeProcess "dot" ["-Tsvg"]
          $ dotGraph title False url dg
        case exCode of
          ExitSuccess -> liftR $ extractSVG dg out
          _ -> fail err

enrichSVG :: DGraph -> Element -> Element
enrichSVG dg e = processSVG dg $ fromElement e

processSVG :: DGraph -> Cursor -> Element
processSVG dg c = case nextDF c of
  Nothing -> case toTree (root c) of
    Elem e -> e
    _ -> error "processSVG"
  Just c2 -> processSVG dg
    $ modifyContent (addSVGAttribs dg) c2

nodeAttrib :: DGNodeLab -> String
nodeAttrib l = let nt = getRealDGNodeType l in
  (if isRefType nt then "Ref" else "")
  ++ (if hasSenKind (const True) l then
          (if isProvenNode nt then "P" else "Unp") ++ "roven"
          ++ if isProvenCons nt then "Cons" else ""
      else "LocallyEmpty")
  ++ (if isInternalSpec nt then "Internal" else "")
  ++ if labelHasHiding l then "HasIngoingHidingLink" else ""

edgeAttrib :: DGLinkLab -> String
edgeAttrib l = show (pretty $ dgl_type l) ++
  if dglPending l then "IncompleteProofChain" else ""

addSVGAttribs :: DGraph -> Content -> Content
addSVGAttribs dg c = case c of
  Elem e -> case getAttrVal "id" e of
    Just istr | isNat istr -> let i = read istr in
      case getAttrVal "class" e of
      Just "node" -> case lab (dgBody dg) i of
        Nothing -> c
        Just l -> Elem $ add_attr (mkAttr "type" $ nodeAttrib l) e
      Just "edge" -> case getDGLinksById (EdgeId i) dg of
        [(_, _, l)] ->
           Elem $ add_attr (mkAttr "type" $ edgeAttrib l) e
        _ -> c
      _ -> c
    _ -> c
  _ -> c

extractSVG :: DGraph -> String -> Result String
extractSVG dg str = case parseXMLDoc str of
  Nothing -> fail "did not recognize svg element"
  Just e -> return $ showTopElement $ enrichSVG dg e

cmpFilePath :: FilePath -> FilePath -> Ordering
cmpFilePath f1 f2 = case comparing hasTrailingPathSeparator f2 f1 of
  EQ -> compare f1 f2
  c -> c

getHetsResponse :: HetcatsOpts -> [FileInfo BS.ByteString]
  -> Cache -> [String] -> [QueryPair] -> WebResponse
getHetsResponse opts updates sessRef pathBits query respond = do
  Result ds ms <- liftIO $ runResultT $ case anaUri pathBits query
    $ updateS : globalCommands of
    Left err -> fail err
    Right q -> getHetsResult opts updates sessRef q Nothing OldWebAPI
                  proofFormatterOptions
  respond $ case ms of
    Just (t, s) | not $ hasErrors ds -> mkOkResponse t s
    _ -> mkResponse textC status422 $ showRelDiags 1 ds

getHetsResult :: HetcatsOpts -> [FileInfo BS.ByteString]
  -> Cache -> Query.Query -> Maybe String -> UsedAPI -> ProofFormatterOptions
  -> ResultT IO (String, String)
getHetsResult opts updates sessRef (Query dgQ qk) format api pfOptions = do
      sk@(sess, k) <- getDGraph opts sessRef dgQ
      let libEnv = sessLibEnv sess
      (ln, dg) <- maybe (fail "unknown development graph") return
        $ sessGraph dgQ sess
      let title = libToFileName ln
      let svg = getSVG title ('/' : show k) dg
      case qk of
            DisplayQuery ms -> case format `mplus` ms of
              Just "svg" -> fmap (\ s -> (svgC, s)) svg
              Just "xml" -> liftR $ return (xmlC, ppTopElement
                $ ToXml.dGraph opts libEnv ln dg)
              Just "json" -> liftR $ return (jsonC, ppJson
                $ ToJson.dGraph opts libEnv ln dg)
              Just "dot" -> liftR $ return
                (dotC, dotGraph title False title dg)
              Just "symbols" -> liftR $ return (xmlC, ppTopElement
                $ ToXml.dgSymbols dg)
              Just "session" -> liftR $ return (htmlC, ppElement
                $ aRef (mkPath sess ln k) $ show k)
              Just str | elem str ppList
                -> ppDGraph dg $ lookup str $ zip ppList prettyList
              _ -> sessAns ln svg sk
            GlProvers mp mt -> do
              availableProvers <- liftIO $ getFullProverList mp mt dg
              return $ case api of
                OldWebAPI -> (xmlC, formatProvers mp $
                  proversToStringAux availableProvers)
                RESTfulAPI -> OProvers.formatProvers format mp availableProvers
            GlTranslations -> do
              availableComorphisms <- liftIO $ getFullComorphList dg
              return $ case api of
                OldWebAPI ->
                  (xmlC, formatComorphs availableComorphisms)
                RESTfulAPI ->
                  formatTranslations format availableComorphisms
            GlShowProverWindow prOrCons -> showAutoProofWindow dg k prOrCons
            GlAutoProve (ProveCmd prOrCons incl mp mt tl nds xForm axioms) -> do
              (newLib, nodesAndProofResults) <-
                proveMultiNodes prOrCons libEnv ln dg incl mp mt tl nds axioms
              if all (null . snd) nodesAndProofResults
                then return (textC, "nothing to prove")
                else do
                lift $ nextSess sess sessRef newLib k
                return $ case api of
                  OldWebAPI -> let
                    sens = foldr (\ (dgNodeName, proofResults) res ->
                        formatResultsAux xForm prOrCons dgNodeName proofResults
                        : res
                      ) [] nodesAndProofResults
                    in (htmlC, formatResultsMultiple xForm k sens prOrCons)
                  RESTfulAPI -> formatProofs
                    format
                    pfOptions
                    nodesAndProofResults
            GlobCmdQuery s ->
              case find ((s ==) . cmdlGlobCmd . fst) allGlobLibAct of
              Nothing -> if s == updateS then
                case filter ((== ".xupdate") . takeExtension . B8.unpack
                            . fileName) updates of
                ch : _ -> do
                  let str = BS.unpack $ fileContent ch
                  (newLn, newLib) <- dgXUpdate opts str libEnv ln dg
                  newSess <- lift $ nextSess sess sessRef newLib k
                  sessAns newLn svg (newSess, k)
                [] -> sessAns ln svg sk
                else fail "getHetsResult.GlobCmdQuery"
              Just (_, act) -> do
                newLib <- liftR $ act ln libEnv
                newSess <- lift $ nextSess sess sessRef newLib k
                -- calculate updated SVG-view from modified development graph
                let newSvg = getSVG title ('/' : show k)
                      $ lookupDGraph ln newLib
                sessAns ln newSvg (newSess, k)
            NodeQuery ein nc -> do
              nl@(i, dgnode) <- case ein of
                Right n -> case lookupNodeByName n dg of
                  p : _ -> return p
                  [] -> fail $ "no node name: " ++ n
                Left i -> case lab (dgBody dg) i of
                  Nothing -> fail $ "no node id: " ++ show i
                  Just dgnode -> return (i, dgnode)
              let fstLine = (if isDGRef dgnode then ("reference " ++) else
                    if isInternalNode dgnode then ("internal " ++) else id)
                    "node " ++ getDGNodeName dgnode ++ " (#" ++ show i ++ ")\n"
                  ins = getImportNames dg i
                  showN d = showGlobalDoc (globalAnnos dg) d "\n"
              case nc of
                NcCmd cmd | elem cmd [Query.Node, Info, Symbols]
                  -> case cmd of
                   Symbols -> return (xmlC, ppTopElement
                           $ showSymbols ins (globalAnnos dg) dgnode)
                   _ -> return (textC, fstLine ++ showN dgnode)
                _ -> case maybeResult $ getGlobalTheory dgnode of
                  Nothing -> fail $
                    "cannot compute global theory of:\n" ++ fstLine
                  Just gTh -> let subL = sublogicOfTh gTh in case nc of
                    ProveNode (ProveCmd pm incl mp mt tl thms xForm axioms) ->
                      case pm of
                      GlProofs -> do
                        (newLib, proofResults) <- proveNode libEnv ln dg nl
                          gTh subL incl mp mt tl thms axioms
                        if null proofResults
                          then return (textC, "nothing to prove")
                          else do
                          lift $ nextSess sess sessRef newLib k
                          return $ case api of
                            OldWebAPI -> (htmlC,
                              formatResults xForm k i . unode "results" $
                                formatGoals True proofResults)
                            RESTfulAPI -> formatProofs
                              format
                              pfOptions
                              [(getDGNodeName dgnode, proofResults)]
                      GlConsistency -> do
                        (newLib, [(_, res, txt, _, _, _)]) <-
                          consNode libEnv ln dg nl subL incl mp mt tl
                        lift $ nextSess sess sessRef newLib k
                        return (xmlC, ppTopElement $ formatConsNode res txt)
                    _ -> case nc of
                      NcCmd Query.Theory -> lift $ fmap (\ t -> (htmlC, t))
                          $ showGlobalTh dg i gTh k fstLine
                      NcProvers mp mt -> do
                        availableProvers <- liftIO $ getProverList mp mt subL
                        return $ case api of
                          OldWebAPI -> (xmlC, formatProvers mp $
                            proversToStringAux availableProvers)
                          RESTfulAPI ->
                            OProvers.formatProvers format mp availableProvers
                      NcTranslations mp -> do
                        availableComorphisms <- liftIO $ getComorphs mp subL
                        return $ case api of
                          OldWebAPI ->
                            (xmlC, formatComorphs availableComorphisms)
                          RESTfulAPI ->
                            formatTranslations format availableComorphisms
                      _ -> error "getHetsResult.NodeQuery."
            EdgeQuery i _ ->
              case getDGLinksById (EdgeId i) dg of
              [e@(_, _, l)] ->
                return (textC, showLEdge e ++ "\n" ++ showDoc l "")
              [] -> fail $ "no edge found with id: " ++ show i
              _ -> fail $ "multiple edges found with id: " ++ show i

formatGoals :: Bool -> [ProofResult] -> [Element]
formatGoals includeDetails =
  map (\ (n, e, d, _, _, mps) -> unode "goal"
    ([unode "name" n, unode "result" e]
    ++ [unode "details" d | includeDetails]
    ++ case mps of
        Nothing -> []
        Just ps -> formatProofStatus ps))

formatProofStatus :: ProofStatus G_proof_tree -> [Element]
formatProofStatus ps =
  [ unode "usedProver" $ usedProver ps
  -- `read` makes this type-unsafe
  , unode "tacticScript" $ formatTacticScript $ read $
      (\ (TacticScript ts) -> ts) $ tacticScript ps
  , unode "proofTree" $ show $ proofTree ps
  , unode "usedTime" $ formatUsedTime $ usedTime ps
  , unode "usedAxioms" $ formatUsedAxioms $ usedAxioms ps
  , unode "proverOutput" $ formatProverOutput $ proofLines ps
  ]

formatProverOutput :: [String] -> CData
formatProverOutput ls =
  CData { cdVerbatim = CDataVerbatim
        , cdData = unlines ls
        , cdLine = Nothing
        }

formatTacticScript :: ATPTacticScript -> [Element]
formatTacticScript ts =
  [ unode "timeLimit" $ show $ tsTimeLimit ts
  , unode "extraOpts" $ map (unode "option") $ tsExtraOpts ts
  ]

formatUsedTime :: TimeOfDay -> [Element]
formatUsedTime tod =
  [ unode "seconds" $ init $ show $ timeOfDayToTime tod
  , unode "components"
    [ unode "hours" $ show $ todHour tod
    , unode "minutes" $ show $ todMin tod
    , unode "seconds" $ show $ todSec tod
    ]
  ]

formatUsedAxioms :: [String] -> [Element]
formatUsedAxioms = map (unode "axiom")

formatConsNode :: String -> String -> Element
formatConsNode res txt = add_attr (mkAttr "state" res) $ unode "result" txt

formatResultsMultiple :: Bool -> Int -> [Element] -> ProverMode -> String
formatResultsMultiple xForm sessId rs prOrCons =
  if xForm then ppTopElement $ unode "Results" rs else let
  goBack1 = case prOrCons of
    GlConsistency -> aRef ('/' : show sessId ++ "?consistency") "return"
    GlProofs -> aRef ('/' : show sessId ++ "?autoproof") "return"
  goBack2 = aRef ('/' : show sessId) "return to DGraph"
  in ppElement $ unode "html" ( unode "head"
    [ unode "title" "Results", add_attr ( mkAttr "type" "text/css" )
    $ unode "style" resultStyles, goBack1, plain " ", goBack2 ]
    : foldr (\ el r -> unode "h4" (qName $ elName el) : el : r) [] rs )

-- | display results of proving session (single node)
formatResults :: Bool -> Int -> Int -> Element -> String
formatResults xForm sessId i rs =
  if xForm || sessId <= 0 then ppTopElement rs else let
  goBack1 = aRef ('/' : show sessId ++ "?theory=" ++ show i) "return to Theory"
  goBack2 = aRef ('/' : show sessId) "return to DGraph"
  in ppElement $ unode "html" [ unode "head"
    [ unode "title" "Results", add_attr ( mkAttr "type" "text/css" )
    $ unode "style" resultStyles, goBack1, plain " ", goBack2 ], rs ]

resultStyles :: String
resultStyles = unlines
  [ "results { margin: 5px; padding:5px; display:block; }"
  , "goal { display:block; margin-left:15px; }"
  , "name { display:inline; margin:5px; padding:10px; font-weight:bold; }"
  , "result { display:inline; padding:30px; }" ]

showBool :: Bool -> String
showBool = map toLower . show

{- | displays the global theory for a node with the option to prove theorems
and select proving options -}
showGlobalTh :: DGraph -> Int -> G_theory -> Int -> String -> IO String
showGlobalTh dg i gTh sessId fstLine = case simplifyTh gTh of
  sGTh@(G_theory lid _ (ExtSign sig _) _ thsens _) -> let
    ga = globalAnnos dg
    -- links to translations and provers xml view
    transBt = aRef ('/' : show sessId ++ "?translations=" ++ show i)
      "translations"
    prvsBt = aRef ('/' : show sessId ++ "?provers=" ++ show i) "provers"
    headr = unode "h3" fstLine
    thShow = renderHtml ga $ vcat $ map (print_named lid) $ toNamedList thsens
    sbShow = renderHtml ga $ pretty sig
    in case getThGoals sGTh of
      -- show simple view if no goals are found
      [] -> return $ mkHtmlElem fstLine [ headr, transBt, prvsBt,
        unode "h4" "Theory" ] ++ sbShow ++ "\n<br />" ++ thShow
      -- else create proving functionality
      gs -> do
        -- create list of theorems, selectable for proving
        let thmSl = map (\ (nm, bp) ->
              let gSt = maybe GOpen basicProofToGStatus bp
              in add_attrs
                 [ mkAttr "type" "checkbox", mkAttr "name" $ escStr nm
                 , mkAttr "unproven" $ showBool $ elem gSt [GOpen, GTimeout]]
              $ unode "input" $ nm ++ "   (" ++ showSimple gSt ++ ")" ) gs
        -- select unproven, all or none theorems by button
            (btUnpr, btAll, btNone, jvScr1) = showSelectionButtons True
        -- create prove button and prover/comorphism selection
        (prSl, cmrSl, jvScr2) <- showProverSelection GlProofs [sublogicOfTh gTh]
        let (prBt, timeout) = showProveButton True
        -- hidden param field
            hidStr = add_attrs [ mkAttr "name" "prove"
              , mkAttr "type" "hidden", mkAttr "style" "display:none;"
              , mkAttr "value" $ show i ] inputNode
        -- combine elements within a form
            thmMenu = let br = unode "br " () in add_attrs
              [ mkAttr "name" "thmSel", mkAttr "method" "get"]
              . unode "form"
              $ [hidStr, prSl, cmrSl, br, btUnpr, btAll, btNone, timeout]
              ++ intersperse br (prBt : thmSl)
        -- save dg and return to svg-view
            goBack = aRef ('/' : show sessId) "return to DGraph"
        return $ mkHtmlElemScript fstLine (jvScr1 ++ jvScr2)
          [ headr, transBt, prvsBt, plain " ", goBack, unode "h4" "Theorems"
          , thmMenu, unode "h4" "Theory" ] ++ sbShow ++ "\n<br />" ++ thShow

-- | show window of the autoproof function
showAutoProofWindow :: DGraph -> Int -> ProverMode
  -> ResultT IO (String, String)
showAutoProofWindow dg sessId prOrCons = let
  dgnodes = labNodesDG dg
  -- some parameters need to be different for consistency and autoproof mode
  (prMethod, isProver, title, nodeSel) = case prOrCons of
    GlProofs -> ("proof", True, "automatic proofs"
      , map (\ fn -> add_attrs [ mkAttr "type" "checkbox"
      , mkAttr "unproven" $ showBool $ not $ allProved fn
      , mkAttr "name" $ escStr $ name fn ]
      $ unode "input" $ showHtml fn) $ initFNodes dgnodes)
    -- TODO sort out nodes with no sentences!
    GlConsistency -> ("cons", False, "consistency checker"
      , map (\ (_, dgn) ->
      let cstat = getConsistencyOf dgn
          nm = getDGNodeName dgn in add_attrs [ mkAttr "type" "checkbox"
      , mkAttr "unproven" $ showBool $ sType cstat == CSUnchecked
      , mkAttr "name" nm]
      $ unode "input" (cStatusToPrefix cstat ++ nm)) dgnodes)
  -- generate param field for the query string, invisible to the user
  hidStr = add_attrs [ mkAttr "name" "autoproof"
         , mkAttr "type" "hidden", mkAttr "style" "display:none;"
         , mkAttr "value" prMethod ] inputNode
  -- select unproven, all or no nodes by button
  (btUnpr, btAll, btNone, jvScr1) = showSelectionButtons isProver
  (prBt, timeout) = showProveButton isProver
  include = add_attrs [ mkAttr "type" "checkbox", mkAttr "checked" "true"
          , mkAttr "name" "includetheorems"] $ unode "input" "include Theorems"
  goBack = aRef ('/' : show sessId) "return to DGraph"
  in do
    (jvScr2, nodeMenu) <- case dgnodes of
      -- return simple feedback if no nodes are present
      [] -> return ("", plain "nothing to prove (graph has no nodes)")
      -- otherwise
      (_, nd) : _ -> case maybeResult $ getGlobalTheory nd of
        Nothing -> fail $ "cannot compute global theory of:\n" ++ show nd
        Just gTh -> do
          let br = unode "br " ()
          (prSel, cmSel, jvSc) <- lift $ showProverSelection prOrCons
              [sublogicOfTh gTh]
          return (jvSc, add_attrs
            [ mkAttr "name" "nodeSel", mkAttr "method" "get" ]
            . unode "form" $
            [ hidStr, prSel, cmSel, br, btAll, btNone, btUnpr, timeout
            , include ] ++ intersperse br (prBt : nodeSel))
    return (htmlC, mkHtmlElemScript title (jvScr1 ++ jvScr2)
               [ goBack, plain " ", nodeMenu ])

showProveButton :: Bool -> (Element, Element)
showProveButton isProver = (prBt, timeout) where
        prBt = [ mkAttr "type" "submit", mkAttr "value"
               $ if isProver then "Prove" else "Check"]
               `add_attrs` inputNode
        -- create timeout field
        timeout = add_attrs [mkAttr "type" "text", mkAttr "name" "timeout"
               , mkAttr "value" "1", mkAttr "size" "3"]
               $ unode "input" "Sec/Goal "

-- | select unproven, all or none theorems by button
showSelectionButtons :: Bool -> (Element, Element, Element, String)
showSelectionButtons isProver = (selUnPr, selAll, selNone, jvScr)
  where prChoice = if isProver then "SPASS" else "darwin"
        selUnPr = add_attrs [mkAttr "type" "button"
          , mkAttr "value" $ if isProver then "Unproven" else "Unchecked"
          , mkAttr "onClick" "chkUnproven()"] inputNode
        selAll = add_attrs [mkAttr "type" "button", mkAttr "value" "All"
          , mkAttr "onClick" "chkAll(true)"] inputNode
        selNone = add_attrs [mkAttr "type" "button", mkAttr "value" "None"
          , mkAttr "onClick" "chkAll(false)"] inputNode
        -- javascript features
        jvScr = unlines
          -- select unproven goals by button
          [ "\nfunction chkUnproven() {"
          , "  var e = document.forms[0].elements;"
          , "  for (i = 0; i < e.length; i++) {"
          , "    if( e[i].type == 'checkbox'"
          , "      && e[i].name != 'includetheorems' )"
          , "      e[i].checked = e[i].getAttribute('unproven') == 'true';"
          , "  }"
          -- select or deselect all theorems by button
          , "}\nfunction chkAll(b) {"
          , "  var e = document.forms[0].elements;"
          , "  for (i = 0; i < e.length; i++) {"
          , "    if( e[i].type == 'checkbox'"
          , "      && e[i].name != 'includetheorems' ) e[i].checked = b;"
          , "  }"
          -- autoselect SPASS if possible
          , "}\nwindow.onload = function() {"
          , "  prSel = document.forms[0].elements.namedItem('prover');"
          , "  prs = prSel.getElementsByTagName('option');"
          , "  for ( i=0; i<prs.length; i++ ) {"
          , "    if( prs[i].value == '" ++ prChoice ++ "' ) {"
          , "      prs[i].selected = 'selected';"
          , "      updCmSel('" ++ prChoice ++ "');"
          , "      return;"
          , "    }"
          , "  }"
          -- if SPASS unable, select first one in list
          , "  prs[0].selected = 'selected';"
          , "  updCmSel( prs[0].value );"
          , "}" ]

-- | create prover and comorphism menu and combine them using javascript
showProverSelection :: ProverMode -> [G_sublogics]
  -> IO (Element, Element, String)
showProverSelection prOrCons subLs = do
  let jvScr = unlines
        -- the chosen prover is passed as param
        [ "\nfunction updCmSel(pr) {"
        , "  var cmrSl = document.forms[0].elements.namedItem('translation');"
        -- then, all selectable comorphisms are gathered and iterated
        , "  var opts = cmrSl.getElementsByTagName('option');"
        -- try to keep current comorph-selection
        , "  var selAccept = false;"
        , "  for( var i = opts.length-1; i >= 0; i-- ) {"
        , "    var cmr = opts.item( i );"
        -- the list of supported provers is extracted
        , "    var prs = cmr.getAttribute('4prover').split(';');"
        , "    var pFit = false;"
        , "    for( var j = 0; ! pFit && j < prs.length; j++ ) {"
        , "      pFit = prs[j] == pr;"
        , "    }"
        -- if prover is supported, remove disabled attribute
        , "    if( pFit ) {"
        , "        cmr.removeAttribute('disabled');"
        , "        selAccept = selAccept || cmr.selected;"
        -- else create and append a disabled attribute
        , "    } else {"
        , "      var ds = document.createAttribute('disabled');"
        , "      ds.value = 'disabled';"
        , "      cmr.setAttributeNode(ds);"
        , "    }"
        , "  }"
        -- check if selected comorphism fits, and select fst. in list otherwise
        , "  if( ! selAccept ) {"
        , "    for( i = 0; i < opts.length; i++ ) {"
        , "      if( ! opts.item(i).disabled ) {"
        , "        opts.item(i).selected = 'selected';"
        , "        return;"
        , "      }"
        , "    }"
        , "  }"
        , "}" ]
  pcs <- mapM (liftM proversToStringAux . (case prOrCons of
    GlProofs -> getProversAux
    GlConsistency -> getConsCheckersAux) Nothing) subLs
  let allPrCm = nub $ concat pcs
  -- create prover selection (drop-down)
      prs = add_attr (mkAttr "name" "prover") $ unode "select" $ map (\ p ->
        add_attrs [mkAttr "value" p, mkAttr "onClick"
                  $ "updCmSel('" ++ p ++ "')"]
        $ unode "option" p) $ showProversOnly allPrCm
  -- create comorphism selection (drop-down)
      cmrs = add_attr (mkAttr "name" "translation") $ unode "select"
        $ map (\ (cm, ps) -> let c = showComorph cm in
        add_attrs [mkAttr "value" c, mkAttr "4prover" $ intercalate ";" ps]
          $ unode "option" c) allPrCm
  return (prs, cmrs, jvScr)

showHtml :: FNode -> String
showHtml fn = name fn ++ " " ++ goalsToPrefix (toGtkGoals fn)

getAllAutomaticProvers :: G_sublogics -> IO [(G_prover, AnyComorphism)]
getAllAutomaticProvers subL =
  getUsableProvers ProveCMDLautomatic subL logicGraph

filterByProver :: Maybe String -> [(G_prover, AnyComorphism)]
  -> [(G_prover, AnyComorphism)]
filterByProver mp = case mp of
      Nothing -> id
      Just p -> filter ((== p) . mkNiceProverName . getProverName . fst)

filterByComorph :: Maybe String -> [(a, AnyComorphism)]
  -> [(a, AnyComorphism)]
filterByComorph mt = case mt of
      Nothing -> id
      Just c -> filter ((== c) . showComorph . snd)

getProverAndComorph :: Maybe String -> Maybe String -> G_sublogics
   -> IO [(G_prover, AnyComorphism)]
getProverAndComorph mp mc subL = do
   ps <- getFilteredProvers mc subL
   let spps = case filterByProver (Just "SPASS") ps of
          [] -> ps
          fps -> fps
   return $ case mp of
        Nothing -> spps
        _ -> filterByProver mp ps

getProverList :: ProverMode -> Maybe String -> G_sublogics
              -> IO [(AnyComorphism, [ProverOrConsChecker])]
getProverList mp mt subL = case mp of
  GlProofs -> getProversAux mt subL
  GlConsistency -> getConsCheckersAux mt subL

getFullProverList :: ProverMode -> Maybe String -> DGraph
                  -> IO [(AnyComorphism, [ProverOrConsChecker])]
getFullProverList mp mt = foldM
  (\ ls (_, nd) -> maybe (return ls) (fmap (++ ls) . case mp of
      GlProofs -> getProversAux mt
      GlConsistency -> getConsCheckersAux mt
    . sublogicOfTh)
    $ maybeResult $ getGlobalTheory nd) [] . labNodesDG

groupOnSnd :: Eq b => (a -> c) -> [(a, b)] -> [(b, [c])]
groupOnSnd f =
  map (\ l@((_, b) : _) -> (b, map (f . fst) l)) . groupBy (on (==) snd)

proversToStringAux :: [(AnyComorphism, [ProverOrConsChecker])]
                   -> [(AnyComorphism, [String])]
proversToStringAux = map (\ (x, ps) ->
                           (x, map (mkNiceProverName . internalProverName) ps))

{- | gather provers and comorphisms and resort them to
(comorhism, supported provers) while not changing orig comorphism order -}
getProversAux :: Maybe String -> G_sublogics
              -> IO [(AnyComorphism, [ProverOrConsChecker])]
getProversAux mt x =
  fmap (groupOnSnd AbsState.Prover) $ getFilteredProvers mt x

getFilteredProvers :: Maybe String -> G_sublogics
  -> IO [(G_prover, AnyComorphism)]
getFilteredProvers mt = fmap (filterByComorph mt) . getAllAutomaticProvers

formatProvers :: ProverMode -> [(AnyComorphism, [String])] -> String
formatProvers pm = let
  tag = case pm of
          GlProofs -> "prover"
          GlConsistency -> "consistency-checker"
  in ppTopElement . unode (tag ++ "s") . map (unode tag)
  . showProversOnly

-- | retrieve a list of consistency checkers
getConsCheckersAux :: Maybe String -> G_sublogics
  -> IO [(AnyComorphism, [ProverOrConsChecker])]
getConsCheckersAux mt =
  fmap (groupOnSnd AbsState.ConsChecker) . getFilteredConsCheckers mt

getFilteredConsCheckers :: Maybe String -> G_sublogics
  -> IO [(G_cons_checker, AnyComorphism)]
getFilteredConsCheckers mt = fmap
  (filterByComorph mt . filter (getCcBatch . fst))
  . getConsCheckers . findComorphismPaths logicGraph

getComorphs :: Maybe String -> G_sublogics -> IO [(G_prover, AnyComorphism)]
getComorphs mp = fmap (filterByProver mp)
    . getAllAutomaticProvers

getFullComorphList :: DGraph -> IO [(G_prover, AnyComorphism)]
getFullComorphList = foldM
   (\ ls (_, nd) -> maybe (return ls)
    (fmap (++ ls) . getAllAutomaticProvers . sublogicOfTh)
    $ maybeResult $ getGlobalTheory nd) [] . labNodesDG

formatComorphs :: [(G_prover, AnyComorphism)] -> String
formatComorphs = ppTopElement . unode "translations"
    . map (unode "comorphism") . nubOrd . map (showComorph . snd)

consNode :: LibEnv -> LibName -> DGraph -> (Int, DGNodeLab)
  -> G_sublogics -> Bool -> Maybe String -> Maybe String -> Maybe Int
  -> ResultT IO (LibEnv, [ProofResult])
consNode le ln dg nl@(i, lb) subL useTh mp mt tl = do
  consList <- lift $ getFilteredConsCheckers mt subL
  let findCC x = filter ((== x ) . getCcName . fst) consList
      mcc = maybe (findCC "darwin") findCC mp
  case mcc of
        [] -> fail "no cons checker found"
        ((cc, c) : _) -> lift $ do
          cstat <- consistencyCheck useTh cc c ln le dg nl $ fromMaybe 1 tl
          -- Consistency Results are stored in LibEnv via DGChange object
          let cSt = sType cstat
              le'' = if cSt == CSUnchecked then le else
                     Map.insert ln (changeDGH dg $ SetNodeLab lb
                       (i, case cSt of
                             CSInconsistent -> markNodeInconsistent "" lb
                             CSConsistent -> markNodeConsistent "" lb
                             _ -> lb)) le
          return (le'', [(" ", drop 2 $ show cSt, show cstat,
                          AbsState.ConsChecker cc, c, Nothing)])

proveNode :: LibEnv -> LibName -> DGraph -> (Int, DGNodeLab) -> G_theory
  -> G_sublogics -> Bool -> Maybe String -> Maybe String -> Maybe Int
  -> [String] -> [String] -> ResultT IO (LibEnv, [ProofResult])
proveNode le ln dg nl gTh subL useTh mp mt tl thms axioms = do
 ps <- lift $ getProverAndComorph mp mt subL
 case ps of
  [] -> fail "no matching translation or prover found"
  cp : _ -> do
    let ks = map fst $ getThGoals gTh
        diffs = Set.difference (Set.fromList thms)
                $ Set.fromList ks
    unless (Set.null diffs) . fail $ "unknown theorems: " ++ show diffs
    when (null thms && null ks) $ fail "no theorems to prove"
    ((nTh, sens), (_, proofStatuses)) <- autoProofAtNode useTh
                                            (maybe 1 (max 1) tl)
      (if null thms then ks else thms) axioms gTh cp
    return (if null sens then le else
        Map.insert ln ( updateLabelTheory le dg nl nTh) le
                      , combineToProofResult sens cp proofStatuses
                      )

combineToProofResult :: [(String, String, String)] -> (G_prover, AnyComorphism)
  -> [ProofStatus G_proof_tree] -> [ProofResult]
combineToProofResult sens (prover, comorphism) proofStatuses = let
  findProofStatusByName :: String -> Maybe (ProofStatus G_proof_tree)
  findProofStatusByName n =
    case filter ((n ==) . goalName) proofStatuses of
      [] -> Nothing
      (ps : _) -> Just ps
  combineSens :: (String, String, String) -> ProofResult
  combineSens (n, e, d) = (n, e, d, AbsState.Prover prover, comorphism,
                           findProofStatusByName n)
  in map combineSens sens

-- run over multiple dgnodes and prove available goals for each
proveMultiNodes :: ProverMode -> LibEnv -> LibName -> DGraph -> Bool
  -> Maybe String -> Maybe String -> Maybe Int -> [String] -> [String]
  -> ResultT IO (LibEnv, [(String, [ProofResult])])
proveMultiNodes pm le ln dg useTh mp mt tl nodeSel axioms = let
  runProof :: LibEnv -> G_theory -> (Int, DGNodeLab)
    -> ResultT IO (LibEnv, [ProofResult])
  runProof le' gTh nl = let
    subL = sublogicOfTh gTh
    dg' = lookupDGraph ln le' in case pm of
    GlConsistency -> consNode le' ln dg' nl subL useTh mp mt tl
    GlProofs ->
      proveNode le' ln dg' nl gTh subL useTh mp mt tl
        (map fst $ getThGoals gTh) axioms
  nodes2check = filter (case nodeSel of
    [] -> case pm of
            GlConsistency -> const True
            GlProofs -> hasOpenGoals . snd
    _ -> (`elem` nodeSel) . getDGNodeName . snd) $ labNodesDG dg
  in foldM
  (\ (le', res) nl@(_, dgn) -> case maybeResult $ getGlobalTheory dgn of
      Nothing -> fail $
                    "cannot compute global theory of:\n" ++ show dgn
      Just gTh -> do
        (le'', proofResults) <- runProof le' gTh nl
        return (le'', (getDGNodeName dgn, proofResults) : res))
          (le, []) nodes2check

formatResultsAux :: Bool -> ProverMode -> String -> [ProofResult] -> Element
formatResultsAux xF pm nm sens = unode nm $ case (sens, pm) of
    ([(_, e, d, _, _, _)], GlConsistency) | xF -> formatConsNode e d
    _ -> unode "results" $ formatGoals xF sens

mkPath :: Session -> LibName -> Int -> String
mkPath sess l k =
        '/' : concat [ libToFileName l ++ "?session="
                     | l /= sessLibName sess ]
        ++ show k

extPath :: Session -> LibName -> Int -> String
extPath sess l k = mkPath sess l k ++
        if l /= sessLibName sess then "&" else "?"

globalCommands :: [String]
globalCommands = map (cmdlGlobCmd . fst) allGlobLibAct

sessAns :: LibName -> ResultT IO String -> (Session, Int)
  -> ResultT IO (String, String)
sessAns libName svgComp (sess, k) =
  svgComp >>= \ svg -> return $ sessAnsAux libName svg (sess, k)

sessAnsAux :: LibName -> String -> (Session, Int) -> (String, String)
sessAnsAux libName svg (sess, k) =
  let libEnv = sessLibEnv sess
      ln = libToFileName libName
      libref l =
        aRef (mkPath sess l k) (libToFileName l) : map (\ d ->
         aRef (extPath sess l k ++ d) d) displayTypes
      libPath = extPath sess libName k
      ref d = aRef (libPath ++ d) d
      autoProofBt = aRef ('/' : show k ++ "?autoproof") "automatic proofs"
      consBt = aRef ('/' : show k ++ "?consistency") "consistency checker"
-- the html quicklinks to nodes and edges have been removed with R.16827
  in (htmlC, htmlHead ++ mkHtmlElem
           ('(' : shows k ")" ++ ln)
           (bold ("library " ++ ln)
            : map ref displayTypes
            ++ menuElement : loadXUpdate (libPath ++ updateS)
            : plain "tools:" : mkUnorderedList [autoProofBt, consBt]
            : plain "commands:"
            : mkUnorderedList (map ref globalCommands)
            : plain "imported libraries:"
            : [mkUnorderedList $ map libref $ Map.keys libEnv]
           ) ++ svg)

getHetsLibContent :: HetcatsOpts -> String -> [QueryPair] -> IO [Element]
getHetsLibContent opts dir query = do
  let hlibs = libdirs opts
  ds <- if null dir || isAbsolute dir then return hlibs else
       filterM doesDirectoryExist $ map (</> dir) hlibs
  fs <- fmap (sortBy cmpFilePath . filter (not . isPrefixOf ".") . concat)
    $ mapM getDirContents ds
  return $ map (mkHtmlRef query) $ getParent dir : fs

getParent :: String -> String
getParent = addTrailingPathSeparator . ("/" </>) . takeDirectory
  . dropTrailingPathSeparator

-- | a variant that adds a trailing slash
getDirContents :: FilePath -> IO [FilePath]
getDirContents d = do
    fs <- getDirectoryContents d
    mapM (\ f -> doesDirectoryExist (d </> f) >>= \ b -> return
            $ if b then addTrailingPathSeparator f else f) fs

aRef :: String -> String -> Element
aRef lnk txt = add_attr (mkAttr "href" lnk) $ unode "a" txt

mkHtmlRef :: [QueryPair] -> String -> Element
mkHtmlRef query entry = unode "dir" $ aRef
  (entry ++ if null query then "" else '?' : intercalate "&"
         (map (\ (x, ms) -> x ++ maybe "" ('=' :) ms) query)) entry

mkUnorderedList :: Node t => [t] -> Element
mkUnorderedList = unode "ul" . map (unode "li")

italic :: String -> Element
italic = unode "i"

bold :: String -> Element
bold = unode "b"

plain :: String -> Element
plain = unode "p"

headElems :: String -> [Element]
headElems path = let d = "default" in unode "strong" "Choose a display type:" :
  map (\ q -> aRef (if q == d then "/" </> path else '?' : q) q)
      (d : displayTypes)
  ++ [ unode "p"
       [ unode "small" "internal command overview as XML:"
       , menuElement ]
     , plain $ "Select a local file as library or "
       ++ "enter a HetCASL specification in the text area and press \"submit\""
       ++ ", or browse through our Hets-lib library below."
     , uploadHtml ]

menuElement :: Element
menuElement = aRef "?menus" "menus"

htmlHead :: String
htmlHead =
    let dtd = "PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\""
        url = "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\""
    in concat ["<!DOCTYPE html ", dtd, " ", url, ">\n"]

inputNode :: Element
inputNode = unode "input" ()

loadNode :: String -> Element
loadNode nm = add_attrs
    [ mkAttr "type" "file"
    , mkAttr "name" nm
    , mkAttr "size" "40"]
    inputNode

submitNode :: Element
submitNode = add_attrs
    [ mkAttr "type" "submit"
    , mkAttr "value" "submit"]
    inputNode

mkForm :: String -> [Element] -> Element
mkForm a = add_attrs
  [ mkAttr "action" a
  , mkAttr "enctype" "multipart/form-data"
  , mkAttr "method" "post" ]
  . unode "form"

uploadHtml :: Element
uploadHtml = mkForm "/"
  [ loadNode "file"
  , unode "p" $ add_attrs
    [ mkAttr "cols" "68"
    , mkAttr "rows" "22"
    , mkAttr "name" "content" ] $ unode "textarea" ""
  , submitNode ]

loadXUpdate :: String -> Element
loadXUpdate a = mkForm a
  [ italic xupdateS
  , loadNode xupdateS
  , italic "impacts"
  , loadNode "impacts"
  , submitNode ]
